import NetHack.Soko22Hazard87.AndIntroBlocks0290
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro72750 (p : Pattern) (ha : d284695 p = 1) (hb : d287269 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d284554 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d284633 q = 1) (hb : d285963 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d284633, d285963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72746 q ha hb
    | true =>
      simp only [d284633, d285963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72747 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d284635 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d284636 q = 1) (hb : d285964 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d284636, d285964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d284636, d285964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d284637 q = 1) (hb : d287251 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d284637, d287251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d284637, d287251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d284638 q = 1) (hb : d287252 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d284638, d287252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d284638, d287252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d284642 q = 1) (hb : d287254 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d284642, d287254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d284642, d287254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72748 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d284644 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d284645 q = 1) (hb : d287255 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d284645, d287255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d284645, d287255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d284646 q = 1) (hb : d287256 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d284646, d287256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d284646, d287256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d284647 q = 1) (hb : d287257 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d284647, d287257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d284647, d287257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d284648 q = 1) (hb : d287258 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d284648, d287258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d284648, d287258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d284684 q = 1) (hb : d287264 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d284684, d287264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d284684, d287264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72749 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d284690 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d284691 q = 1) (hb : d287265 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d284691, d287265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d284691, d287265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d284692 q = 1) (hb : d287266 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d284692, d287266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d284692, d287266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d284693 q = 1) (hb : d287267 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d284693, d287267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d284693, d287267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d284694 q = 1) (hb : d287268 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d284694, d287268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d284694, d287268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d284695 q = 1) (hb : d287269 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d284695, d287269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d284695, d287269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro72751 (p : Pattern) (ha : d284701 p = 1) (hb : d287275 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d284696 q = 1) (hb : d287270 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d284696, d287270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d284696, d287270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72750 q ha hb
  have h2 (q : Pattern) (ha : d284697 q = 1) (hb : d287271 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d284697, d287271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d284697, d287271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d284698 q = 1) (hb : d287272 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d284698, d287272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d284698, d287272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d284699 q = 1) (hb : d287273 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d284699, d287273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d284699, d287273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d284700 q = 1) (hb : d287274 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d284700, d287274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d284700, d287274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d284701 q = 1) (hb : d287275 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d284701, d287275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d284701, d287275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72752 (p : Pattern) (ha : d284816 p = 1) (hb : d286127 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d284746 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d284755 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d284805 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d284720 q = 1) (hb : d286122 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d284720, d286122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72488 q ha hb
    | true =>
      simp only [d284720, d286122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72489 q ha hb
  have h5 (q : Pattern) (ha : d284806 q = 1) (hb : d286123 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d284806, d286123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d284806, d286123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d284812 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d284813 q = 1) (hb : d286124 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d284813, d286124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d284813, d286124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d284814 q = 1) (hb : d286125 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d284814, d286125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d284814, d286125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d284815 q = 1) (hb : d286126 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d284815, d286126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d284815, d286126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d284816 q = 1) (hb : d286127 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d284816, d286127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d284816, d286127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro72753 (p : Pattern) (ha : d284837 p = 1) (hb : d286137 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d284746 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d284755 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d284805 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d284720 q = 1) (hb : d286122 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d284720, d286122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72488 q ha hb
    | true =>
      simp only [d284720, d286122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72489 q ha hb
  have h4 (q : Pattern) (ha : d284806 q = 1) (hb : d286123 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d284806, d286123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d284806, d286123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d284812 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d284813 q = 1) (hb : d286124 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d284813, d286124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d284813, d286124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d284814 q = 1) (hb : d286125 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d284814, d286125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d284814, d286125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d284815 q = 1) (hb : d286126 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d284815, d286126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d284815, d286126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d284822 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d284827 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d284829 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d284730 q = 1) (hb : d286132 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d284730, d286132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72491 q ha hb
    | true =>
      simp only [d284730, d286132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72492 q ha hb
  have h13 (q : Pattern) (ha : d284830 q = 1) (hb : d286133 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d284830, d286133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d284830, d286133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d284833 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d284834 q = 1) (hb : d286134 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d284834, d286134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d284834, d286134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d284835 q = 1) (hb : d286135 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d284835, d286135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d284835, d286135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d284836 q = 1) (hb : d286136 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d284836, d286136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d284836, d286136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d284837 q = 1) (hb : d286137 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d284837, d286137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d284837, d286137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro72754 (p : Pattern) (ha : d284857 p = 1) (hb : d287279 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d284829 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d284730 q = 1) (hb : d286132 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d284730, d286132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72491 q ha hb
    | true =>
      simp only [d284730, d286132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72492 q ha hb
  have h3 (q : Pattern) (ha : d284830 q = 1) (hb : d286133 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d284830, d286133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d284830, d286133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d284833 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d284834 q = 1) (hb : d286134 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d284834, d286134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d284834, d286134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d284855 q = 1) (hb : d286135 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d284855, d286135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d284855, d286135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d284856 q = 1) (hb : d286136 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d284856, d286136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d284856, d286136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d284857 q = 1) (hb : d287279 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d284857, d287279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d284857, d287279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72755 (p : Pattern) (ha : d284925 p = 1) (hb : d287290 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d284909 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d284914 q = 1) (hb : d287285 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d284914, d287285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72526 q ha hb
    | true =>
      simp only [d284914, d287285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72529 q ha hb
  have h3 (q : Pattern) (ha : d284915 q = 1) (hb : d287286 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d284915, d287286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d284915, d287286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d284921 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d284922 q = 1) (hb : d287287 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d284922, d287287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d284922, d287287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d284923 q = 1) (hb : d287288 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d284923, d287288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d284923, d287288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d284924 q = 1) (hb : d287289 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d284924, d287289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d284924, d287289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d284925 q = 1) (hb : d287290 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d284925, d287290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d284925, d287290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72756 (p : Pattern) (ha : d284938 p = 1) (hb : d287296 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d284738 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d284838 q = 1) (hb : d286138 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d284838, d286138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72752 q ha hb
    | true =>
      simp only [d284838, d286138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72753 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d284851 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d284852 q = 1) (hb : d286139 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d284852, d286139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d284852, d286139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d284853 q = 1) (hb : d287277 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d284853, d287277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d284853, d287277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d284854 q = 1) (hb : d287278 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d284854, d287278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d284854, d287278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d284858 q = 1) (hb : d287280 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d284858, d287280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d284858, d287280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72754 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d284860 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d284861 q = 1) (hb : d287281 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d284861, d287281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d284861, d287281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d284862 q = 1) (hb : d287282 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d284862, d287282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d284862, d287282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d284863 q = 1) (hb : d287283 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d284863, d287283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d284863, d287283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d284864 q = 1) (hb : d287284 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d284864, d287284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d284864, d287284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d284926 q = 1) (hb : d287291 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d284926, d287291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d284926, d287291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72755 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d284933 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d284934 q = 1) (hb : d287292 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d284934, d287292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d284934, d287292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d284935 q = 1) (hb : d287293 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d284935, d287293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d284935, d287293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d284936 q = 1) (hb : d287294 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d284936, d287294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d284936, d287294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d284937 q = 1) (hb : d287295 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d284937, d287295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d284937, d287295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d284938 q = 1) (hb : d287296 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d284938, d287296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d284938, d287296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro72757 (p : Pattern) (ha : d284944 p = 1) (hb : d287302 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d284939 q = 1) (hb : d287297 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d284939, d287297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d284939, d287297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72756 q ha hb
  have h2 (q : Pattern) (ha : d284940 q = 1) (hb : d287298 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d284940, d287298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d284940, d287298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d284941 q = 1) (hb : d287299 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d284941, d287299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d284941, d287299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d284942 q = 1) (hb : d287300 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d284942, d287300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d284942, d287300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d284943 q = 1) (hb : d287301 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d284943, d287301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d284943, d287301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d284944 q = 1) (hb : d287302 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d284944, d287302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d284944, d287302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72758 (p : Pattern) (ha : d285071 p = 1) (hb : d286382 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d285008 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d285017 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d285060 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d284982 q = 1) (hb : d286377 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d284982, d286377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72539 q ha hb
    | true =>
      simp only [d284982, d286377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72540 q ha hb
  have h5 (q : Pattern) (ha : d285061 q = 1) (hb : d286378 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d285061, d286378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d285061, d286378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d285067 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d285068 q = 1) (hb : d286379 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d285068, d286379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d285068, d286379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d285069 q = 1) (hb : d286380 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d285069, d286380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d285069, d286380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d285070 q = 1) (hb : d286381 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d285070, d286381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d285070, d286381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d285071 q = 1) (hb : d286382 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d285071, d286382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285071, d286382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro72759 (p : Pattern) (ha : d285092 p = 1) (hb : d286392 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d285008 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d285017 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d285060 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d284982 q = 1) (hb : d286377 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d284982, d286377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72539 q ha hb
    | true =>
      simp only [d284982, d286377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72540 q ha hb
  have h4 (q : Pattern) (ha : d285061 q = 1) (hb : d286378 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d285061, d286378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d285061, d286378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d285067 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d285068 q = 1) (hb : d286379 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d285068, d286379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d285068, d286379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d285069 q = 1) (hb : d286380 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d285069, d286380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d285069, d286380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d285070 q = 1) (hb : d286381 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d285070, d286381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285070, d286381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d285077 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d285082 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d285084 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d284992 q = 1) (hb : d286387 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d284992, d286387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72542 q ha hb
    | true =>
      simp only [d284992, d286387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72543 q ha hb
  have h13 (q : Pattern) (ha : d285085 q = 1) (hb : d286388 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d285085, d286388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d285085, d286388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d285088 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d285089 q = 1) (hb : d286389 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d285089, d286389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d285089, d286389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d285090 q = 1) (hb : d286390 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d285090, d286390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d285090, d286390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d285091 q = 1) (hb : d286391 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d285091, d286391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d285091, d286391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d285092 q = 1) (hb : d286392 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d285092, d286392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d285092, d286392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro72760 (p : Pattern) (ha : d285112 p = 1) (hb : d287307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d285084 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d284992 q = 1) (hb : d286387 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d284992, d286387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72542 q ha hb
    | true =>
      simp only [d284992, d286387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72543 q ha hb
  have h3 (q : Pattern) (ha : d285085 q = 1) (hb : d286388 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d285085, d286388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d285085, d286388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d285088 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d285089 q = 1) (hb : d286389 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d285089, d286389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d285089, d286389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d285110 q = 1) (hb : d286390 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d285110, d286390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285110, d286390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d285111 q = 1) (hb : d286391 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d285111, d286391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285111, d286391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d285112 q = 1) (hb : d287307 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d285112, d287307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285112, d287307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72761 (p : Pattern) (ha : d285197 p = 1) (hb : d287318 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d285181 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d285186 q = 1) (hb : d287313 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d285186, d287313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72578 q ha hb
    | true =>
      simp only [d285186, d287313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72581 q ha hb
  have h3 (q : Pattern) (ha : d285187 q = 1) (hb : d287314 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d285187, d287314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d285187, d287314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d285193 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d285194 q = 1) (hb : d287315 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d285194, d287315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d285194, d287315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d285195 q = 1) (hb : d287316 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d285195, d287316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285195, d287316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d285196 q = 1) (hb : d287317 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d285196, d287317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285196, d287317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d285197 q = 1) (hb : d287318 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d285197, d287318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285197, d287318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72762 (p : Pattern) (ha : d285210 p = 1) (hb : d287324 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d285000 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285093 q = 1) (hb : d286393 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285093, d286393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72758 q ha hb
    | true =>
      simp only [d285093, d286393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72759 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d285106 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d285107 q = 1) (hb : d286394 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d285107, d286394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d285107, d286394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d285108 q = 1) (hb : d287305 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d285108, d287305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d285108, d287305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d285109 q = 1) (hb : d287306 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d285109, d287306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285109, d287306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d285113 q = 1) (hb : d287308 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285113, d287308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d285113, d287308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72760 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d285115 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d285116 q = 1) (hb : d287309 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d285116, d287309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d285116, d287309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d285117 q = 1) (hb : d287310 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d285117, d287310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d285117, d287310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d285118 q = 1) (hb : d287311 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d285118, d287311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d285118, d287311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d285119 q = 1) (hb : d287312 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d285119, d287312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d285119, d287312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d285198 q = 1) (hb : d287319 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285198, d287319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d285198, d287319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72761 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d285205 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d285206 q = 1) (hb : d287320 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d285206, d287320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d285206, d287320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d285207 q = 1) (hb : d287321 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d285207, d287321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d285207, d287321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d285208 q = 1) (hb : d287322 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d285208, d287322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d285208, d287322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d285209 q = 1) (hb : d287323 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d285209, d287323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d285209, d287323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d285210 q = 1) (hb : d287324 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d285210, d287324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d285210, d287324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro72763 (p : Pattern) (ha : d285216 p = 1) (hb : d287330 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285211 q = 1) (hb : d287325 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d285211, d287325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285211, d287325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72762 q ha hb
  have h2 (q : Pattern) (ha : d285212 q = 1) (hb : d287326 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d285212, d287326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285212, d287326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d285213 q = 1) (hb : d287327 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d285213, d287327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285213, d287327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d285214 q = 1) (hb : d287328 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d285214, d287328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285214, d287328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d285215 q = 1) (hb : d287329 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d285215, d287329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285215, d287329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d285216 q = 1) (hb : d287330 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d285216, d287330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285216, d287330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72764 (p : Pattern) (ha : d285367 p = 1) (hb : d286685 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d285317 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d285326 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d285356 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d285291 q = 1) (hb : d286680 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d285291, d286680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72596 q ha hb
    | true =>
      simp only [d285291, d286680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72597 q ha hb
  have h5 (q : Pattern) (ha : d285357 q = 1) (hb : d286681 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d285357, d286681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d285357, d286681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d285363 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d285364 q = 1) (hb : d286682 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d285364, d286682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d285364, d286682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d285365 q = 1) (hb : d286683 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d285365, d286683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d285365, d286683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d285366 q = 1) (hb : d286684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d285366, d286684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d285366, d286684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d285367 q = 1) (hb : d286685 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d285367, d286685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285367, d286685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro72765 (p : Pattern) (ha : d285388 p = 1) (hb : d286695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d285317 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d285326 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d285356 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d285291 q = 1) (hb : d286680 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d285291, d286680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72596 q ha hb
    | true =>
      simp only [d285291, d286680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72597 q ha hb
  have h4 (q : Pattern) (ha : d285357 q = 1) (hb : d286681 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d285357, d286681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d285357, d286681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d285363 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d285364 q = 1) (hb : d286682 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d285364, d286682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d285364, d286682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d285365 q = 1) (hb : d286683 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d285365, d286683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d285365, d286683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d285366 q = 1) (hb : d286684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d285366, d286684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285366, d286684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d285373 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d285378 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d285380 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d285301 q = 1) (hb : d286690 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d285301, d286690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72599 q ha hb
    | true =>
      simp only [d285301, d286690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72600 q ha hb
  have h13 (q : Pattern) (ha : d285381 q = 1) (hb : d286691 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d285381, d286691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d285381, d286691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d285384 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d285385 q = 1) (hb : d286692 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d285385, d286692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d285385, d286692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d285386 q = 1) (hb : d286693 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d285386, d286693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d285386, d286693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d285387 q = 1) (hb : d286694 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d285387, d286694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d285387, d286694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d285388 q = 1) (hb : d286695 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d285388, d286695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d285388, d286695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro72766 (p : Pattern) (ha : d285408 p = 1) (hb : d287336 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d285380 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d285301 q = 1) (hb : d286690 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d285301, d286690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72599 q ha hb
    | true =>
      simp only [d285301, d286690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72600 q ha hb
  have h3 (q : Pattern) (ha : d285381 q = 1) (hb : d286691 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d285381, d286691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d285381, d286691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d285384 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d285385 q = 1) (hb : d286692 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d285385, d286692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d285385, d286692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d285406 q = 1) (hb : d286693 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d285406, d286693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285406, d286693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d285407 q = 1) (hb : d286694 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d285407, d286694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285407, d286694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d285408 q = 1) (hb : d287336 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d285408, d287336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285408, d287336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72767 (p : Pattern) (ha : d285506 p = 1) (hb : d287347 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d285490 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d285495 q = 1) (hb : d287342 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d285495, d287342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72634 q ha hb
    | true =>
      simp only [d285495, d287342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72637 q ha hb
  have h3 (q : Pattern) (ha : d285496 q = 1) (hb : d287343 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d285496, d287343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d285496, d287343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d285502 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d285503 q = 1) (hb : d287344 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d285503, d287344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d285503, d287344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d285504 q = 1) (hb : d287345 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d285504, d287345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285504, d287345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d285505 q = 1) (hb : d287346 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d285505, d287346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285505, d287346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d285506 q = 1) (hb : d287347 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d285506, d287347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285506, d287347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72768 (p : Pattern) (ha : d285519 p = 1) (hb : d287353 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d285309 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285389 q = 1) (hb : d286696 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285389, d286696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72764 q ha hb
    | true =>
      simp only [d285389, d286696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72765 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d285402 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d285403 q = 1) (hb : d286697 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d285403, d286697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d285403, d286697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d285404 q = 1) (hb : d287334 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d285404, d287334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d285404, d287334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d285405 q = 1) (hb : d287335 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d285405, d287335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285405, d287335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d285409 q = 1) (hb : d287337 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285409, d287337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d285409, d287337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72766 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d285411 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d285412 q = 1) (hb : d287338 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d285412, d287338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d285412, d287338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d285413 q = 1) (hb : d287339 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d285413, d287339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d285413, d287339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d285414 q = 1) (hb : d287340 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d285414, d287340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d285414, d287340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d285415 q = 1) (hb : d287341 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d285415, d287341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d285415, d287341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d285507 q = 1) (hb : d287348 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285507, d287348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d285507, d287348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72767 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d285514 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d285515 q = 1) (hb : d287349 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d285515, d287349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d285515, d287349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d285516 q = 1) (hb : d287350 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d285516, d287350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d285516, d287350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d285517 q = 1) (hb : d287351 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d285517, d287351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d285517, d287351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d285518 q = 1) (hb : d287352 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d285518, d287352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d285518, d287352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d285519 q = 1) (hb : d287353 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d285519, d287353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d285519, d287353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro72769 (p : Pattern) (ha : d285525 p = 1) (hb : d287359 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285520 q = 1) (hb : d287354 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d285520, d287354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285520, d287354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72768 q ha hb
  have h2 (q : Pattern) (ha : d285521 q = 1) (hb : d287355 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d285521, d287355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285521, d287355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d285522 q = 1) (hb : d287356 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d285522, d287356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285522, d287356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d285523 q = 1) (hb : d287357 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d285523, d287357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285523, d287357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d285524 q = 1) (hb : d287358 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d285524, d287358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285524, d287358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d285525 q = 1) (hb : d287359 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d285525, d287359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285525, d287359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72770 (p : Pattern) (ha : d285665 p = 1) (hb : d286977 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d285611 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d285620 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d285635 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d285585 q = 1) (hb : d286972 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d285585, d286972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72651 q ha hb
    | true =>
      simp only [d285585, d286972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72652 q ha hb
  have h5 (q : Pattern) (ha : d285636 q = 1) (hb : d286973 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d285636, d286973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d285636, d286973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d285661 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d285662 q = 1) (hb : d286974 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d285662, d286974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d285662, d286974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d285663 q = 1) (hb : d286975 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d285663, d286975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d285663, d286975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d285664 q = 1) (hb : d286976 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d285664, d286976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d285664, d286976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d285665 q = 1) (hb : d286977 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d285665, d286977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285665, d286977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro72771 (p : Pattern) (ha : d285686 p = 1) (hb : d286987 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d285611 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d285620 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d285635 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d285585 q = 1) (hb : d286972 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d285585, d286972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72651 q ha hb
    | true =>
      simp only [d285585, d286972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72652 q ha hb
  have h4 (q : Pattern) (ha : d285636 q = 1) (hb : d286973 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d285636, d286973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d285636, d286973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d285661 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d285662 q = 1) (hb : d286974 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d285662, d286974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d285662, d286974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d285663 q = 1) (hb : d286975 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d285663, d286975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d285663, d286975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d285664 q = 1) (hb : d286976 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d285664, d286976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285664, d286976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d285671 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d285676 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d285678 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d285595 q = 1) (hb : d286982 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d285595, d286982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72654 q ha hb
    | true =>
      simp only [d285595, d286982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72655 q ha hb
  have h13 (q : Pattern) (ha : d285679 q = 1) (hb : d286983 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d285679, d286983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d285679, d286983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d285682 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d285683 q = 1) (hb : d286984 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d285683, d286984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d285683, d286984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d285684 q = 1) (hb : d286985 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d285684, d286985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d285684, d286985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d285685 q = 1) (hb : d286986 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d285685, d286986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d285685, d286986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d285686 q = 1) (hb : d286987 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d285686, d286987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d285686, d286987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro72772 (p : Pattern) (ha : d285706 p = 1) (hb : d287366 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d285678 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d285595 q = 1) (hb : d286982 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d285595, d286982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72654 q ha hb
    | true =>
      simp only [d285595, d286982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72655 q ha hb
  have h3 (q : Pattern) (ha : d285679 q = 1) (hb : d286983 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d285679, d286983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d285679, d286983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d285682 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d285683 q = 1) (hb : d286984 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d285683, d286984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d285683, d286984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d285704 q = 1) (hb : d286985 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d285704, d286985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285704, d286985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d285705 q = 1) (hb : d286986 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d285705, d286986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285705, d286986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d285706 q = 1) (hb : d287366 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d285706, d287366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285706, d287366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72773 (p : Pattern) (ha : d285797 p = 1) (hb : d287377 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d285766 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d285771 q = 1) (hb : d287372 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d285771, d287372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72689 q ha hb
    | true =>
      simp only [d285771, d287372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72695 q ha hb
  have h3 (q : Pattern) (ha : d285772 q = 1) (hb : d287373 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d285772, d287373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d285772, d287373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d285793 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d285794 q = 1) (hb : d287374 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d285794, d287374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d285794, d287374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d285795 q = 1) (hb : d287375 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d285795, d287375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285795, d287375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d285796 q = 1) (hb : d287376 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d285796, d287376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285796, d287376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d285797 q = 1) (hb : d287377 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d285797, d287377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285797, d287377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72774 (p : Pattern) (ha : d285810 p = 1) (hb : d287383 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d285603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285687 q = 1) (hb : d286988 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285687, d286988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72770 q ha hb
    | true =>
      simp only [d285687, d286988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72771 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d285700 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d285701 q = 1) (hb : d286989 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d285701, d286989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d285701, d286989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d285702 q = 1) (hb : d287364 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d285702, d287364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d285702, d287364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d285703 q = 1) (hb : d287365 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d285703, d287365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285703, d287365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d285707 q = 1) (hb : d287367 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285707, d287367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d285707, d287367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72772 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d285709 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d285710 q = 1) (hb : d287368 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d285710, d287368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d285710, d287368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d285711 q = 1) (hb : d287369 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d285711, d287369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d285711, d287369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d285712 q = 1) (hb : d287370 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d285712, d287370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d285712, d287370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d285713 q = 1) (hb : d287371 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d285713, d287371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d285713, d287371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d285798 q = 1) (hb : d287378 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285798, d287378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d285798, d287378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72773 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d285805 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d285806 q = 1) (hb : d287379 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d285806, d287379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d285806, d287379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d285807 q = 1) (hb : d287380 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d285807, d287380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d285807, d287380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d285808 q = 1) (hb : d287381 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d285808, d287381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d285808, d287381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d285809 q = 1) (hb : d287382 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d285809, d287382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d285809, d287382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d285810 q = 1) (hb : d287383 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d285810, d287383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d285810, d287383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro72775 (p : Pattern) (ha : d285816 p = 1) (hb : d287389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285811 q = 1) (hb : d287384 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d285811, d287384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285811, d287384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72774 q ha hb
  have h2 (q : Pattern) (ha : d285812 q = 1) (hb : d287385 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d285812, d287385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285812, d287385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d285813 q = 1) (hb : d287386 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d285813, d287386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285813, d287386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d285814 q = 1) (hb : d287387 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d285814, d287387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285814, d287387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d285815 q = 1) (hb : d287388 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d285815, d287388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285815, d287388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d285816 q = 1) (hb : d287389 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d285816, d287389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d285816, d287389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72776 (p : Pattern) (ha : d285822 p = 1) (hb : d287395 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d284702 q = 1) (hb : d287276 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d284702, d287276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72745 q hb ha
    | true =>
      simp only [d284702, d287276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72751 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d284945 q = 1) (hb : d287303 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d284945, d287303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d284945, d287303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72757 q ha hb
  have h3 (q : Pattern) (ha : d284946 q = 1) (hb : d287304 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d284946, d287304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d284946, d287304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d285217 q = 1) (hb : d287331 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d285217, d287331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d285217, d287331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72763 q ha hb
  have h5 (q : Pattern) (ha : d285218 q = 1) (hb : d287332 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d285218, d287332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d285218, d287332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d285219 q = 1) (hb : d287333 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d285219, d287333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d285219, d287333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d285526 q = 1) (hb : d287360 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d285526, d287360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d285526, d287360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72769 q ha hb
  have h8 (q : Pattern) (ha : d285527 q = 1) (hb : d287361 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d285527, d287361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d285527, d287361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d285528 q = 1) (hb : d287362 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d285528, d287362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d285528, d287362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d285529 q = 1) (hb : d287363 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d285529, d287363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d285529, d287363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d285817 q = 1) (hb : d287390 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d285817, d287390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d285817, d287390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72775 q ha hb
  have h12 (q : Pattern) (ha : d285818 q = 1) (hb : d287391 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d285818, d287391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d285818, d287391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d285819 q = 1) (hb : d287392 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d285819, d287392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d285819, d287392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d285820 q = 1) (hb : d287393 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d285820, d287393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d285820, d287393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d285821 q = 1) (hb : d287394 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d285821, d287394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d285821, d287394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d285822 q = 1) (hb : d287395 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d285822, d287395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d285822, d287395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro72777 (p : Pattern) (ha : d285828 p = 1) (hb : d287401 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285823 q = 1) (hb : d287396 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d285823, d287396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72776 q ha hb
    | true =>
      simp only [d285823, d287396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d285824 q = 1) (hb : d287397 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d285824, d287397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d285824, d287397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d285825 q = 1) (hb : d287398 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d285825, d287398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d285825, d287398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d285826 q = 1) (hb : d287399 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d285826, d287399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d285826, d287399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d285827 q = 1) (hb : d287400 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d285827, d287400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d285827, d287400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d285828 q = 1) (hb : d287401 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d285828, d287401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d285828, d287401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro72778 (p : Pattern) (ha : d285834 p = 1) (hb : d287407 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285829 q = 1) (hb : d287402 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d285829, d287402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72777 q ha hb
    | true =>
      simp only [d285829, d287402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d285830 q = 1) (hb : d287403 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d285830, d287403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d285830, d287403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d285831 q = 1) (hb : d287404 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d285831, d287404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d285831, d287404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d285832 q = 1) (hb : d287405 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d285832, d287405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d285832, d287405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d285833 q = 1) (hb : d287406 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d285833, d287406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d285833, d287406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d285834 q = 1) (hb : d287407 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d285834, d287407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d285834, d287407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro72779 (p : Pattern) (ha : d285840 p = 1) (hb : d287413 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285835 q = 1) (hb : d287408 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d285835, d287408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72778 q ha hb
    | true =>
      simp only [d285835, d287408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d285836 q = 1) (hb : d287409 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d285836, d287409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d285836, d287409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d285837 q = 1) (hb : d287410 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d285837, d287410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d285837, d287410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d285838 q = 1) (hb : d287411 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d285838, d287411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d285838, d287411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d285839 q = 1) (hb : d287412 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d285839, d287412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d285839, d287412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d285840 q = 1) (hb : d287413 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d285840, d287413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d285840, d287413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro72780 (p : Pattern) (ha : d285846 p = 1) (hb : d287419 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285841 q = 1) (hb : d287414 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d285841, d287414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72779 q ha hb
    | true =>
      simp only [d285841, d287414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d285842 q = 1) (hb : d287415 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d285842, d287415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d285842, d287415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d285843 q = 1) (hb : d287416 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d285843, d287416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d285843, d287416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d285844 q = 1) (hb : d287417 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d285844, d287417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d285844, d287417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d285845 q = 1) (hb : d287418 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d285845, d287418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d285845, d287418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d285846 q = 1) (hb : d287419 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d285846, d287419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d285846, d287419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro72781 (p : Pattern) (ha : d285852 p = 1) (hb : d287425 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285847 q = 1) (hb : d287420 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d285847, d287420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72780 q ha hb
    | true =>
      simp only [d285847, d287420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d285848 q = 1) (hb : d287421 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d285848, d287421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d285848, d287421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d285849 q = 1) (hb : d287422 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d285849, d287422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d285849, d287422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d285850 q = 1) (hb : d287423 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d285850, d287423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d285850, d287423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d285851 q = 1) (hb : d287424 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d285851, d287424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d285851, d287424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d285852 q = 1) (hb : d287425 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d285852, d287425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d285852, d287425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro72782 (p : Pattern) (ha : d285858 p = 1) (hb : d287431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285853 q = 1) (hb : d287426 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d285853, d287426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72781 q ha hb
    | true =>
      simp only [d285853, d287426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d285854 q = 1) (hb : d287427 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d285854, d287427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d285854, d287427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d285855 q = 1) (hb : d287428 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d285855, d287428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d285855, d287428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d285856 q = 1) (hb : d287429 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d285856, d287429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d285856, d287429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d285857 q = 1) (hb : d287430 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d285857, d287430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d285857, d287430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d285858 q = 1) (hb : d287431 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d285858, d287431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d285858, d287431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro72783 (p : Pattern) (ha : d285864 p = 1) (hb : d287437 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285859 q = 1) (hb : d287432 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d285859, d287432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72782 q ha hb
    | true =>
      simp only [d285859, d287432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d285860 q = 1) (hb : d287433 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d285860, d287433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d285860, d287433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d285861 q = 1) (hb : d287434 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d285861, d287434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d285861, d287434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d285862 q = 1) (hb : d287435 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d285862, d287435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d285862, d287435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d285863 q = 1) (hb : d287436 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d285863, d287436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d285863, d287436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d285864 q = 1) (hb : d287437 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d285864, d287437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d285864, d287437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro72784 (p : Pattern) (ha : d257269 p = 1) (hb : d287442 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d282387 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282393 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d282418 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d257207 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d257265 q = 1) (hb : d287438 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d257265, d287438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257265, d287438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d282310 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d257266 q = 1) (hb : d287439 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d257266, d287439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d257266, d287439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d257267 q = 1) (hb : d287440 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d257267, d287440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d257267, d287440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d257268 q = 1) (hb : d287441 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d257268, d287441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257268, d287441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d257269 q = 1) (hb : d287442 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d257269, d287442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d257269, d287442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro72785 (p : Pattern) (ha : d257276 p = 1) (hb : d287447 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282387 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d282393 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282418 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d257207 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d257265 q = 1) (hb : d287438 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d257265, d287438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d257265, d287438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d282310 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d257266 q = 1) (hb : d287439 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d257266, d287439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d257266, d287439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d257267 q = 1) (hb : d287440 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d257267, d287440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257267, d287440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d257268 q = 1) (hb : d287441 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d257268, d287441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d257268, d287441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d282453 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d282457 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d282459 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d257214 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d257272 q = 1) (hb : d287443 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d257272, d287443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d257272, d287443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d282317 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d257273 q = 1) (hb : d287444 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d257273, d287444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d257273, d287444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d257274 q = 1) (hb : d287445 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d257274, d287445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d257274, d287445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d257275 q = 1) (hb : d287446 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d257275, d287446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d257275, d287446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d257276 q = 1) (hb : d287447 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d257276, d287447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d257276, d287447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro72786 (p : Pattern) (ha : d257490 p = 1) (hb : d287454 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d282459 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d257214 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d257272 q = 1) (hb : d287443 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d257272, d287443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257272, d287443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d282317 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d257273 q = 1) (hb : d287444 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d257273, d287444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257273, d287444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d257274 q = 1) (hb : d287452 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d257274, d287452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d257274, d287452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d257275 q = 1) (hb : d287453 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d257275, d287453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d257275, d287453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d257490 q = 1) (hb : d287454 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d257490, d287454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d257490, d287454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72787 (p : Pattern) (ha : d257536 p = 1) (hb : d287464 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d282499 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d257248 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d257532 q = 1) (hb : d287460 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d257532, d287460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257532, d287460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d282351 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d257533 q = 1) (hb : d287461 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d257533, d287461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257533, d287461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d257534 q = 1) (hb : d287462 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d257534, d287462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d257534, d287462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d257535 q = 1) (hb : d287463 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d257535, d287463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d257535, d287463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d257536 q = 1) (hb : d287464 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d257536, d287464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d257536, d287464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72788 (p : Pattern) (ha : d259893 p = 1) (hb : d287470 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d257277 q = 1) (hb : d287448 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d257277, d287448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72784 q ha hb
    | true =>
      simp only [d257277, d287448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72785 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282469 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d257278 q = 1) (hb : d287449 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d257278, d287449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257278, d287449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d259883 q = 1) (hb : d287450 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d259883, d287450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d259883, d287450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d259884 q = 1) (hb : d287451 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d259884, d287451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259884, d287451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d257491 q = 1) (hb : d287455 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d257491, d287455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d257491, d287455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72786 q ha hb
  have h8 (q : Pattern) (ha : d259885 q = 1) (hb : d287456 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d259885, d287456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d259885, d287456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d259886 q = 1) (hb : d287457 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d259886, d287457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d259886, d287457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d259887 q = 1) (hb : d287458 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d259887, d287458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d259887, d287458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d259888 q = 1) (hb : d287459 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d259888, d287459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d259888, d287459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d257537 q = 1) (hb : d287465 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d257537, d287465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d257537, d287465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72787 q ha hb
  have h13 (q : Pattern) (ha : d259889 q = 1) (hb : d287466 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d259889, d287466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d259889, d287466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d259890 q = 1) (hb : d287467 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d259890, d287467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d259890, d287467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d259891 q = 1) (hb : d287468 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d259891, d287468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d259891, d287468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d259892 q = 1) (hb : d287469 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d259892, d287469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d259892, d287469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d259893 q = 1) (hb : d287470 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d259893, d287470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d259893, d287470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro72789 (p : Pattern) (ha : d259899 p = 1) (hb : d287476 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282366 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d259894 q = 1) (hb : d287471 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d259894, d287471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d259894, d287471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72788 q ha hb
  have h3 (q : Pattern) (ha : d259895 q = 1) (hb : d287472 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d259895, d287472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d259895, d287472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d259896 q = 1) (hb : d287473 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d259896, d287473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d259896, d287473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d259897 q = 1) (hb : d287474 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d259897, d287474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d259897, d287474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d259898 q = 1) (hb : d287475 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d259898, d287475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d259898, d287475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d259899 q = 1) (hb : d287476 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d259899, d287476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259899, d287476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro72790 (p : Pattern) (ha : d285955 p = 1) (hb : d287481 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d282556 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282562 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d282598 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d285890 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d285951 q = 1) (hb : d287477 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d285951, d287477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d285951, d287477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d282630 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d285952 q = 1) (hb : d287478 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d285952, d287478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d285952, d287478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d285953 q = 1) (hb : d287479 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d285953, d287479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d285953, d287479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d285954 q = 1) (hb : d287480 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d285954, d287480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d285954, d287480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d285955 q = 1) (hb : d287481 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d285955, d287481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285955, d287481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro72791 (p : Pattern) (ha : d285962 p = 1) (hb : d287486 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282556 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d282562 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282598 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d285890 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d285951 q = 1) (hb : d287477 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d285951, d287477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d285951, d287477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d282630 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d285952 q = 1) (hb : d287478 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d285952, d287478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d285952, d287478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d285953 q = 1) (hb : d287479 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d285953, d287479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d285953, d287479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d285954 q = 1) (hb : d287480 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d285954, d287480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285954, d287480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d282639 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d282643 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d282645 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d285897 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d285958 q = 1) (hb : d287482 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d285958, d287482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d285958, d287482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d282651 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d285959 q = 1) (hb : d287483 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d285959, d287483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d285959, d287483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d285960 q = 1) (hb : d287484 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d285960, d287484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d285960, d287484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d285961 q = 1) (hb : d287485 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d285961, d287485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d285961, d287485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d285962 q = 1) (hb : d287486 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d285962, d287486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d285962, d287486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro72792 (p : Pattern) (ha : d287253 p = 1) (hb : d287493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d282645 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d285897 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d285958 q = 1) (hb : d287482 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d285958, d287482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d285958, d287482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d282651 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d285959 q = 1) (hb : d287483 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d285959, d287483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d285959, d287483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d285960 q = 1) (hb : d287491 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d285960, d287491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285960, d287491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d285961 q = 1) (hb : d287492 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d285961, d287492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285961, d287492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d287253 q = 1) (hb : d287493 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d287253, d287493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287253, d287493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72793 (p : Pattern) (ha : d287263 p = 1) (hb : d287503 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d282695 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d285933 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d287259 q = 1) (hb : d287499 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287259, d287499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d287259, d287499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d282721 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d287260 q = 1) (hb : d287500 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d287260, d287500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d287260, d287500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d287261 q = 1) (hb : d287501 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d287261, d287501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287261, d287501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d287262 q = 1) (hb : d287502 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d287262, d287502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287262, d287502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d287263 q = 1) (hb : d287503 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d287263, d287503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287263, d287503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72794 (p : Pattern) (ha : d287269 p = 1) (hb : d287509 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282550 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285963 q = 1) (hb : d287487 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285963, d287487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72790 q ha hb
    | true =>
      simp only [d285963, d287487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72791 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282658 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d285964 q = 1) (hb : d287488 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d285964, d287488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d285964, d287488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d287251 q = 1) (hb : d287489 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d287251, d287489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d287251, d287489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d287252 q = 1) (hb : d287490 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d287252, d287490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287252, d287490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d287254 q = 1) (hb : d287494 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d287254, d287494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d287254, d287494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72792 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d282667 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d287255 q = 1) (hb : d287495 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d287255, d287495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d287255, d287495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d287256 q = 1) (hb : d287496 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d287256, d287496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d287256, d287496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d287257 q = 1) (hb : d287497 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d287257, d287497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d287257, d287497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d287258 q = 1) (hb : d287498 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d287258, d287498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d287258, d287498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d287264 q = 1) (hb : d287504 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d287264, d287504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d287264, d287504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72793 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d282732 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d287265 q = 1) (hb : d287505 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d287265, d287505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d287265, d287505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d287266 q = 1) (hb : d287506 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d287266, d287506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d287266, d287506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d287267 q = 1) (hb : d287507 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d287267, d287507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d287267, d287507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d287268 q = 1) (hb : d287508 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d287268, d287508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d287268, d287508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d287269 q = 1) (hb : d287509 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d287269, d287509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d287269, d287509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro72795 (p : Pattern) (ha : d287275 p = 1) (hb : d287515 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d287270 q = 1) (hb : d287510 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d287270, d287510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287270, d287510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72794 q ha hb
  have h2 (q : Pattern) (ha : d287271 q = 1) (hb : d287511 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d287271, d287511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287271, d287511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d287272 q = 1) (hb : d287512 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d287272, d287512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287272, d287512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d287273 q = 1) (hb : d287513 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d287273, d287513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287273, d287513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d287274 q = 1) (hb : d287514 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d287274, d287514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287274, d287514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d287275 q = 1) (hb : d287515 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d287275, d287515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287275, d287515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72796 (p : Pattern) (ha : d286127 p = 1) (hb : d287521 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d282788 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282797 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d282847 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d286122 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d286123 q = 1) (hb : d287517 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d286123, d287517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d286123, d287517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d282899 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d286124 q = 1) (hb : d287518 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d286124, d287518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d286124, d287518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d286125 q = 1) (hb : d287519 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d286125, d287519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d286125, d287519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d286126 q = 1) (hb : d287520 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d286126, d287520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286126, d287520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d286127 q = 1) (hb : d287521 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d286127, d287521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d286127, d287521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro72797 (p : Pattern) (ha : d286137 p = 1) (hb : d287526 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282788 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d282797 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282847 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d286122 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d286123 q = 1) (hb : d287517 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d286123, d287517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d286123, d287517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d282899 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d286124 q = 1) (hb : d287518 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d286124, d287518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d286124, d287518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d286125 q = 1) (hb : d287519 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d286125, d287519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286125, d287519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d286126 q = 1) (hb : d287520 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d286126, d287520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d286126, d287520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d282909 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d282914 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d282916 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d286132 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d286133 q = 1) (hb : d287522 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d286133, d287522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d286133, d287522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d282923 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d286134 q = 1) (hb : d287523 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d286134, d287523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d286134, d287523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d286135 q = 1) (hb : d287524 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d286135, d287524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d286135, d287524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d286136 q = 1) (hb : d287525 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d286136, d287525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d286136, d287525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d286137 q = 1) (hb : d287526 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d286137, d287526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d286137, d287526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro72798 (p : Pattern) (ha : d287279 p = 1) (hb : d287533 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d282916 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d286132 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d286133 q = 1) (hb : d287522 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d286133, d287522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286133, d287522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d282923 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d286134 q = 1) (hb : d287523 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d286134, d287523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d286134, d287523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d286135 q = 1) (hb : d287531 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d286135, d287531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d286135, d287531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d286136 q = 1) (hb : d287532 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d286136, d287532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d286136, d287532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d287279 q = 1) (hb : d287533 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d287279, d287533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287279, d287533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72799 (p : Pattern) (ha : d287290 p = 1) (hb : d287543 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d282999 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d287285 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d287286 q = 1) (hb : d287539 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287286, d287539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d287286, d287539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d283039 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d287287 q = 1) (hb : d287540 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d287287, d287540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d287287, d287540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d287288 q = 1) (hb : d287541 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d287288, d287541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287288, d287541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d287289 q = 1) (hb : d287542 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d287289, d287542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287289, d287542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d287290 q = 1) (hb : d287543 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d287290, d287543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287290, d287543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72800 (p : Pattern) (ha : d287296 p = 1) (hb : d287549 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282780 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d286138 q = 1) (hb : d287527 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d286138, d287527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72796 q ha hb
    | true =>
      simp only [d286138, d287527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72797 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282941 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d286139 q = 1) (hb : d287528 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286139, d287528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286139, d287528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d287277 q = 1) (hb : d287529 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d287277, d287529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d287277, d287529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d287278 q = 1) (hb : d287530 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d287278, d287530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287278, d287530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d287280 q = 1) (hb : d287534 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d287280, d287534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d287280, d287534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72798 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d282950 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d287281 q = 1) (hb : d287535 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d287281, d287535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d287281, d287535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d287282 q = 1) (hb : d287536 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d287282, d287536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d287282, d287536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d287283 q = 1) (hb : d287537 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d287283, d287537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d287283, d287537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d287284 q = 1) (hb : d287538 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d287284, d287538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d287284, d287538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d287291 q = 1) (hb : d287544 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d287291, d287544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d287291, d287544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72799 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d283055 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d287292 q = 1) (hb : d287545 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d287292, d287545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d287292, d287545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d287293 q = 1) (hb : d287546 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d287293, d287546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d287293, d287546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d287294 q = 1) (hb : d287547 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d287294, d287547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d287294, d287547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d287295 q = 1) (hb : d287548 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d287295, d287548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d287295, d287548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d287296 q = 1) (hb : d287549 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d287296, d287549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d287296, d287549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro72801 (p : Pattern) (ha : d287302 p = 1) (hb : d287555 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d287297 q = 1) (hb : d287550 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d287297, d287550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287297, d287550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72800 q ha hb
  have h2 (q : Pattern) (ha : d287298 q = 1) (hb : d287551 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d287298, d287551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287298, d287551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d287299 q = 1) (hb : d287552 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d287299, d287552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287299, d287552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d287300 q = 1) (hb : d287553 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d287300, d287553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287300, d287553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d287301 q = 1) (hb : d287554 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d287301, d287554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287301, d287554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d287302 q = 1) (hb : d287555 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d287302, d287555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287302, d287555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72802 (p : Pattern) (ha : d286382 p = 1) (hb : d287562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d283130 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d283139 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d283182 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d286377 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d286378 q = 1) (hb : d287558 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d286378, d287558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d286378, d287558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d283256 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d286379 q = 1) (hb : d287559 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d286379, d287559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d286379, d287559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d286380 q = 1) (hb : d287560 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d286380, d287560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d286380, d287560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d286381 q = 1) (hb : d287561 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d286381, d287561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286381, d287561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d286382 q = 1) (hb : d287562 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d286382, d287562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d286382, d287562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro72803 (p : Pattern) (ha : d286392 p = 1) (hb : d287567 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d283130 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d283139 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d283182 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d286377 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d286378 q = 1) (hb : d287558 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d286378, d287558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d286378, d287558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d283256 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d286379 q = 1) (hb : d287559 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d286379, d287559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d286379, d287559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d286380 q = 1) (hb : d287560 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d286380, d287560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286380, d287560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d286381 q = 1) (hb : d287561 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d286381, d287561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d286381, d287561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d283266 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d283271 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d283273 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d286387 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d286388 q = 1) (hb : d287563 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d286388, d287563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d286388, d287563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d283280 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d286389 q = 1) (hb : d287564 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d286389, d287564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d286389, d287564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d286390 q = 1) (hb : d287565 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d286390, d287565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d286390, d287565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d286391 q = 1) (hb : d287566 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d286391, d287566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d286391, d287566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d286392 q = 1) (hb : d287567 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d286392, d287567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d286392, d287567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro72804 (p : Pattern) (ha : d287307 p = 1) (hb : d287574 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d283273 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d286387 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d286388 q = 1) (hb : d287563 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d286388, d287563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286388, d287563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d283280 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d286389 q = 1) (hb : d287564 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d286389, d287564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d286389, d287564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d286390 q = 1) (hb : d287572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d286390, d287572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d286390, d287572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d286391 q = 1) (hb : d287573 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d286391, d287573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d286391, d287573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d287307 q = 1) (hb : d287574 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d287307, d287574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287307, d287574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72805 (p : Pattern) (ha : d287318 p = 1) (hb : d287584 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d283373 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d287313 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d287314 q = 1) (hb : d287580 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287314, d287580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d287314, d287580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d283428 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d287315 q = 1) (hb : d287581 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d287315, d287581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d287315, d287581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d287316 q = 1) (hb : d287582 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d287316, d287582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287316, d287582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d287317 q = 1) (hb : d287583 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d287317, d287583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287317, d287583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d287318 q = 1) (hb : d287584 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d287318, d287584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287318, d287584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72806 (p : Pattern) (ha : d287324 p = 1) (hb : d287590 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d283122 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d286393 q = 1) (hb : d287568 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d286393, d287568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72802 q ha hb
    | true =>
      simp only [d286393, d287568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72803 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d283298 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d286394 q = 1) (hb : d287569 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286394, d287569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286394, d287569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d287305 q = 1) (hb : d287570 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d287305, d287570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d287305, d287570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d287306 q = 1) (hb : d287571 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d287306, d287571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287306, d287571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d287308 q = 1) (hb : d287575 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d287308, d287575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d287308, d287575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72804 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d283307 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d287309 q = 1) (hb : d287576 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d287309, d287576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d287309, d287576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d287310 q = 1) (hb : d287577 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d287310, d287577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d287310, d287577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d287311 q = 1) (hb : d287578 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d287311, d287578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d287311, d287578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d287312 q = 1) (hb : d287579 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d287312, d287579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d287312, d287579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d287319 q = 1) (hb : d287585 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d287319, d287585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d287319, d287585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72805 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d283444 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d287320 q = 1) (hb : d287586 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d287320, d287586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d287320, d287586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d287321 q = 1) (hb : d287587 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d287321, d287587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d287321, d287587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d287322 q = 1) (hb : d287588 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d287322, d287588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d287322, d287588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d287323 q = 1) (hb : d287589 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d287323, d287589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d287323, d287589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d287324 q = 1) (hb : d287590 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d287324, d287590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d287324, d287590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro72807 (p : Pattern) (ha : d287330 p = 1) (hb : d287596 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d287325 q = 1) (hb : d287591 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d287325, d287591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287325, d287591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72806 q ha hb
  have h2 (q : Pattern) (ha : d287326 q = 1) (hb : d287592 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d287326, d287592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287326, d287592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d287327 q = 1) (hb : d287593 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d287327, d287593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287327, d287593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d287328 q = 1) (hb : d287594 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d287328, d287594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287328, d287594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d287329 q = 1) (hb : d287595 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d287329, d287595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287329, d287595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d287330 q = 1) (hb : d287596 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d287330, d287596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287330, d287596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72808 (p : Pattern) (ha : d286685 p = 1) (hb : d287604 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d283556 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d283565 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d283595 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d286680 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d286681 q = 1) (hb : d287600 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d286681, d287600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d286681, d287600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d283678 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d286682 q = 1) (hb : d287601 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d286682, d287601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d286682, d287601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d286683 q = 1) (hb : d287602 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d286683, d287602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d286683, d287602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d286684 q = 1) (hb : d287603 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d286684, d287603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286684, d287603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d286685 q = 1) (hb : d287604 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d286685, d287604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d286685, d287604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro72809 (p : Pattern) (ha : d286695 p = 1) (hb : d287609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d283556 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d283565 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d283595 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d286680 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d286681 q = 1) (hb : d287600 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d286681, d287600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d286681, d287600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d283678 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d286682 q = 1) (hb : d287601 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d286682, d287601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d286682, d287601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d286683 q = 1) (hb : d287602 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d286683, d287602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286683, d287602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d286684 q = 1) (hb : d287603 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d286684, d287603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d286684, d287603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d283688 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d283693 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d283695 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d286690 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d286691 q = 1) (hb : d287605 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d286691, d287605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d286691, d287605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d283702 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d286692 q = 1) (hb : d287606 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d286692, d287606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d286692, d287606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d286693 q = 1) (hb : d287607 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d286693, d287607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d286693, d287607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d286694 q = 1) (hb : d287608 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d286694, d287608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d286694, d287608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d286695 q = 1) (hb : d287609 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d286695, d287609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d286695, d287609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro72810 (p : Pattern) (ha : d287336 p = 1) (hb : d287616 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d283695 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d286690 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d286691 q = 1) (hb : d287605 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d286691, d287605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286691, d287605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d283702 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d286692 q = 1) (hb : d287606 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d286692, d287606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d286692, d287606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d286693 q = 1) (hb : d287614 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d286693, d287614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d286693, d287614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d286694 q = 1) (hb : d287615 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d286694, d287615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d286694, d287615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d287336 q = 1) (hb : d287616 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d287336, d287616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287336, d287616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72811 (p : Pattern) (ha : d287347 p = 1) (hb : d287626 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d283808 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d287342 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d287343 q = 1) (hb : d287622 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287343, d287622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d287343, d287622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d283867 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d287344 q = 1) (hb : d287623 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d287344, d287623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d287344, d287623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d287345 q = 1) (hb : d287624 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d287345, d287624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287345, d287624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d287346 q = 1) (hb : d287625 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d287346, d287625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287346, d287625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d287347 q = 1) (hb : d287626 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d287347, d287626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287347, d287626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72812 (p : Pattern) (ha : d287353 p = 1) (hb : d287632 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d283548 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d286696 q = 1) (hb : d287610 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d286696, d287610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72808 q ha hb
    | true =>
      simp only [d286696, d287610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72809 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d283720 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d286697 q = 1) (hb : d287611 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286697, d287611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286697, d287611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d287334 q = 1) (hb : d287612 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d287334, d287612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d287334, d287612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d287335 q = 1) (hb : d287613 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d287335, d287613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287335, d287613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d287337 q = 1) (hb : d287617 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d287337, d287617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d287337, d287617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72810 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d283729 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d287338 q = 1) (hb : d287618 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d287338, d287618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d287338, d287618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d287339 q = 1) (hb : d287619 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d287339, d287619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d287339, d287619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d287340 q = 1) (hb : d287620 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d287340, d287620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d287340, d287620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d287341 q = 1) (hb : d287621 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d287341, d287621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d287341, d287621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d287348 q = 1) (hb : d287627 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d287348, d287627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d287348, d287627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72811 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d283883 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d287349 q = 1) (hb : d287628 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d287349, d287628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d287349, d287628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d287350 q = 1) (hb : d287629 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d287350, d287629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d287350, d287629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d287351 q = 1) (hb : d287630 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d287351, d287630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d287351, d287630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d287352 q = 1) (hb : d287631 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d287352, d287631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d287352, d287631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d287353 q = 1) (hb : d287632 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d287353, d287632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d287353, d287632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro72813 (p : Pattern) (ha : d287359 p = 1) (hb : d287638 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d287354 q = 1) (hb : d287633 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d287354, d287633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287354, d287633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72812 q ha hb
  have h2 (q : Pattern) (ha : d287355 q = 1) (hb : d287634 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d287355, d287634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287355, d287634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d287356 q = 1) (hb : d287635 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d287356, d287635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287356, d287635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d287357 q = 1) (hb : d287636 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d287357, d287636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287357, d287636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d287358 q = 1) (hb : d287637 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d287358, d287637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287358, d287637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d287359 q = 1) (hb : d287638 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d287359, d287638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287359, d287638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72814 (p : Pattern) (ha : d286977 p = 1) (hb : d287647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d283980 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d283989 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d284004 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d286972 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d286973 q = 1) (hb : d287643 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d286973, d287643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d286973, d287643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d284086 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d286974 q = 1) (hb : d287644 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d286974, d287644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d286974, d287644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d286975 q = 1) (hb : d287645 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d286975, d287645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d286975, d287645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d286976 q = 1) (hb : d287646 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d286976, d287646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286976, d287646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d286977 q = 1) (hb : d287647 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d286977, d287647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d286977, d287647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro72815 (p : Pattern) (ha : d286987 p = 1) (hb : d287652 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d283980 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d283989 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d284004 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d286972 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d286973 q = 1) (hb : d287643 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d286973, d287643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d286973, d287643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d284086 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d286974 q = 1) (hb : d287644 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d286974, d287644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d286974, d287644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d286975 q = 1) (hb : d287645 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d286975, d287645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286975, d287645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d286976 q = 1) (hb : d287646 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d286976, d287646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d286976, d287646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d284096 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d284101 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d284103 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d286982 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d286983 q = 1) (hb : d287648 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d286983, d287648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d286983, d287648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d284110 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d286984 q = 1) (hb : d287649 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d286984, d287649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d286984, d287649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d286985 q = 1) (hb : d287650 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d286985, d287650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d286985, d287650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d286986 q = 1) (hb : d287651 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d286986, d287651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d286986, d287651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d286987 q = 1) (hb : d287652 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d286987, d287652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d286987, d287652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro72816 (p : Pattern) (ha : d287366 p = 1) (hb : d287659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d284103 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d286982 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d286983 q = 1) (hb : d287648 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d286983, d287648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286983, d287648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d284110 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d286984 q = 1) (hb : d287649 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d286984, d287649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d286984, d287649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d286985 q = 1) (hb : d287657 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d286985, d287657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d286985, d287657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d286986 q = 1) (hb : d287658 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d286986, d287658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d286986, d287658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d287366 q = 1) (hb : d287659 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d287366, d287659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287366, d287659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72817 (p : Pattern) (ha : d287377 p = 1) (hb : d287669 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d284194 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d287372 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d287373 q = 1) (hb : d287665 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287373, d287665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d287373, d287665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d284259 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d287374 q = 1) (hb : d287666 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d287374, d287666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d287374, d287666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d287375 q = 1) (hb : d287667 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d287375, d287667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287375, d287667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d287376 q = 1) (hb : d287668 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d287376, d287668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287376, d287668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d287377 q = 1) (hb : d287669 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d287377, d287669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287377, d287669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72818 (p : Pattern) (ha : d287383 p = 1) (hb : d287675 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d283972 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d286988 q = 1) (hb : d287653 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d286988, d287653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72814 q ha hb
    | true =>
      simp only [d286988, d287653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72815 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d284128 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d286989 q = 1) (hb : d287654 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286989, d287654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286989, d287654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d287364 q = 1) (hb : d287655 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d287364, d287655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d287364, d287655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d287365 q = 1) (hb : d287656 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d287365, d287656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287365, d287656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d287367 q = 1) (hb : d287660 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d287367, d287660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d287367, d287660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72816 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d284137 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d287368 q = 1) (hb : d287661 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d287368, d287661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d287368, d287661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d287369 q = 1) (hb : d287662 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d287369, d287662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d287369, d287662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d287370 q = 1) (hb : d287663 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d287370, d287663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d287370, d287663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d287371 q = 1) (hb : d287664 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d287371, d287664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d287371, d287664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d287378 q = 1) (hb : d287670 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d287378, d287670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d287378, d287670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72817 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d284275 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d287379 q = 1) (hb : d287671 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d287379, d287671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d287379, d287671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d287380 q = 1) (hb : d287672 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d287380, d287672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d287380, d287672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d287381 q = 1) (hb : d287673 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d287381, d287673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d287381, d287673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d287382 q = 1) (hb : d287674 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d287382, d287674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d287382, d287674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d287383 q = 1) (hb : d287675 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d287383, d287675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d287383, d287675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro72819 (p : Pattern) (ha : d287389 p = 1) (hb : d287681 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d287384 q = 1) (hb : d287676 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d287384, d287676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287384, d287676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72818 q ha hb
  have h2 (q : Pattern) (ha : d287385 q = 1) (hb : d287677 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d287385, d287677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287385, d287677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d287386 q = 1) (hb : d287678 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d287386, d287678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287386, d287678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d287387 q = 1) (hb : d287679 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d287387, d287679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287387, d287679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d287388 q = 1) (hb : d287680 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d287388, d287680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287388, d287680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d287389 q = 1) (hb : d287681 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d287389, d287681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287389, d287681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72820 (p : Pattern) (ha : d287395 p = 1) (hb : d287687 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d287276 q = 1) (hb : d287516 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d287276, d287516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72789 q ha hb
    | true =>
      simp only [d287276, d287516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72795 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d287303 q = 1) (hb : d287556 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d287303, d287556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d287303, d287556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72801 q ha hb
  have h3 (q : Pattern) (ha : d287304 q = 1) (hb : d287557 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d287304, d287557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287304, d287557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d287331 q = 1) (hb : d287597 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d287331, d287597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d287331, d287597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72807 q ha hb
  have h5 (q : Pattern) (ha : d287332 q = 1) (hb : d287598 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d287332, d287598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d287332, d287598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d287333 q = 1) (hb : d287599 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d287333, d287599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d287333, d287599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d287360 q = 1) (hb : d287639 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d287360, d287639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d287360, d287639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72813 q ha hb
  have h8 (q : Pattern) (ha : d287361 q = 1) (hb : d287640 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d287361, d287640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d287361, d287640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d287362 q = 1) (hb : d287641 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d287362, d287641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d287362, d287641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d287363 q = 1) (hb : d287642 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d287363, d287642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d287363, d287642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d287390 q = 1) (hb : d287682 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d287390, d287682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d287390, d287682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72819 q ha hb
  have h12 (q : Pattern) (ha : d287391 q = 1) (hb : d287683 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d287391, d287683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d287391, d287683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d287392 q = 1) (hb : d287684 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d287392, d287684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d287392, d287684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d287393 q = 1) (hb : d287685 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d287393, d287685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d287393, d287685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d287394 q = 1) (hb : d287686 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d287394, d287686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d287394, d287686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d287395 q = 1) (hb : d287687 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d287395, d287687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d287395, d287687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro72821 (p : Pattern) (ha : d287401 p = 1) (hb : d287693 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d287396 q = 1) (hb : d287688 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d287396, d287688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72820 q ha hb
    | true =>
      simp only [d287396, d287688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d287397 q = 1) (hb : d287689 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d287397, d287689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d287397, d287689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d287398 q = 1) (hb : d287690 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d287398, d287690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d287398, d287690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d287399 q = 1) (hb : d287691 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d287399, d287691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d287399, d287691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d287400 q = 1) (hb : d287692 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d287400, d287692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d287400, d287692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d287401 q = 1) (hb : d287693 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d287401, d287693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d287401, d287693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72822 (p : Pattern) (ha : d287407 p = 1) (hb : d287699 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d287402 q = 1) (hb : d287694 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d287402, d287694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72821 q ha hb
    | true =>
      simp only [d287402, d287694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d287403 q = 1) (hb : d287695 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d287403, d287695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d287403, d287695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d287404 q = 1) (hb : d287696 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d287404, d287696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d287404, d287696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d287405 q = 1) (hb : d287697 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d287405, d287697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d287405, d287697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d287406 q = 1) (hb : d287698 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d287406, d287698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d287406, d287698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d287407 q = 1) (hb : d287699 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d287407, d287699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d287407, d287699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72823 (p : Pattern) (ha : d287413 p = 1) (hb : d287705 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d287408 q = 1) (hb : d287700 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d287408, d287700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72822 q ha hb
    | true =>
      simp only [d287408, d287700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d287409 q = 1) (hb : d287701 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d287409, d287701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d287409, d287701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d287410 q = 1) (hb : d287702 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d287410, d287702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d287410, d287702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d287411 q = 1) (hb : d287703 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d287411, d287703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d287411, d287703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d287412 q = 1) (hb : d287704 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d287412, d287704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d287412, d287704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d287413 q = 1) (hb : d287705 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d287413, d287705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d287413, d287705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72824 (p : Pattern) (ha : d287419 p = 1) (hb : d287711 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d287414 q = 1) (hb : d287706 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d287414, d287706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72823 q ha hb
    | true =>
      simp only [d287414, d287706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d287415 q = 1) (hb : d287707 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d287415, d287707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d287415, d287707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d287416 q = 1) (hb : d287708 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d287416, d287708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d287416, d287708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d287417 q = 1) (hb : d287709 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d287417, d287709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d287417, d287709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d287418 q = 1) (hb : d287710 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d287418, d287710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d287418, d287710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d287419 q = 1) (hb : d287711 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d287419, d287711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d287419, d287711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72825 (p : Pattern) (ha : d287425 p = 1) (hb : d287717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d287420 q = 1) (hb : d287712 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d287420, d287712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72824 q ha hb
    | true =>
      simp only [d287420, d287712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d287421 q = 1) (hb : d287713 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d287421, d287713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d287421, d287713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d287422 q = 1) (hb : d287714 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d287422, d287714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d287422, d287714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d287423 q = 1) (hb : d287715 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d287423, d287715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d287423, d287715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d287424 q = 1) (hb : d287716 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d287424, d287716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d287424, d287716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d287425 q = 1) (hb : d287717 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d287425, d287717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d287425, d287717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72826 (p : Pattern) (ha : d287431 p = 1) (hb : d287723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d287426 q = 1) (hb : d287718 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d287426, d287718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72825 q ha hb
    | true =>
      simp only [d287426, d287718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d287427 q = 1) (hb : d287719 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d287427, d287719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d287427, d287719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d287428 q = 1) (hb : d287720 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d287428, d287720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d287428, d287720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d287429 q = 1) (hb : d287721 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d287429, d287721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d287429, d287721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d287430 q = 1) (hb : d287722 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d287430, d287722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d287430, d287722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d287431 q = 1) (hb : d287723 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d287431, d287723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d287431, d287723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72827 (p : Pattern) (ha : d287437 p = 1) (hb : d287729 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d287432 q = 1) (hb : d287724 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d287432, d287724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72826 q ha hb
    | true =>
      simp only [d287432, d287724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d287433 q = 1) (hb : d287725 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d287433, d287725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d287433, d287725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d287434 q = 1) (hb : d287726 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d287434, d287726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d287434, d287726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d287435 q = 1) (hb : d287727 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d287435, d287727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d287435, d287727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d287436 q = 1) (hb : d287728 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d287436, d287728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d287436, d287728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d287437 q = 1) (hb : d287729 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d287437, d287729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d287437, d287729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72828 (p : Pattern) (ha : d138 p = 1) (hb : d266246 p = 1) : d25104 p = 1 := by
  have h0 (q : Pattern) (ha : d134 q = 1) (hb : d236581 q = 1) : d134 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d135 q = 1) (hb : d266244 q = 1) : d9796 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d266244, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d135, d266244, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d21 q = 1) (hb : d266245 q = 1) : d21 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d136 q = 1) (hb : d266246 q = 1) : d25102 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d136, d266246, d25102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d136, d266246, d25102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d137 q = 1) (hb : d266246 q = 1) : d25103 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d137, d25103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137, d25103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23 q = 1) (hb : d266246 q = 1) : d23 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d138 q = 1) (hb : d266246 q = 1) : d25104 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d138, d25104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d138, d25104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72829 (p : Pattern) (ha : d144 p = 1) (hb : d266246 p = 1) : d25110 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d139 q = 1) (hb : d266246 q = 1) : d25105 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d25105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72828 q ha hb
    | true =>
      simp only [d139, d25105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d140 q = 1) (hb : d266246 q = 1) : d25106 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d25106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d140, d25106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d141 q = 1) (hb : d266246 q = 1) : d25107 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d25107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d25107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d142 q = 1) (hb : d266246 q = 1) : d25108 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d25108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d142, d25108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d266246 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d143 q = 1) (hb : d266246 q = 1) : d25109 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d143, d25109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d143, d25109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d266246 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d144 q = 1) (hb : d266246 q = 1) : d25110 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d144, d25110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144, d25110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72830 (p : Pattern) (ha : d150 p = 1) (hb : d266246 p = 1) : d25116 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d266246 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145 q = 1) (hb : d266246 q = 1) : d25111 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d25111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72829 q ha hb
    | true =>
      simp only [d145, d25111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146 q = 1) (hb : d266246 q = 1) : d25112 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d25112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d25112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147 q = 1) (hb : d266246 q = 1) : d25113 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d25113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d25113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d266246 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148 q = 1) (hb : d266246 q = 1) : d25114 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d25114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148, d25114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d266246 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d149 q = 1) (hb : d266246 q = 1) : d25115 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d149, d25115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d149, d25115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150 q = 1) (hb : d266246 q = 1) : d25116 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d150, d25116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150, d25116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro72831 (p : Pattern) (ha : d203 p = 1) (hb : d266246 p = 1) : d25129 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d266246 q = 1) : d25117 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d25117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72830 q ha hb
    | true =>
      simp only [d151, d25117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d266246 q = 1) : d25118 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d25118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d25118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d266246 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d266246 q = 1) : d25119 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d25119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d25119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d266246 q = 1) : d25120 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d25120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d25120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d155 q = 1) (hb : d266246 q = 1) : d25121 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d25121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155, d25121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d203 q = 1) (hb : d266246 q = 1) : d25129 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203, d25129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d203, d25129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro72832 (p : Pattern) (ha : d4349 p = 1) (hb : d266246 p = 1) : d201989 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d266246 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d204 q = 1) (hb : d266246 q = 1) : d25130 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d25130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72831 q ha hb
    | true =>
      simp only [d204, d25130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4340 q = 1) (hb : d266246 q = 1) : d201978 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d201978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4340, d201978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d266246 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4341 q = 1) (hb : d266246 q = 1) : d201979 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d201979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4341, d201979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4342 q = 1) (hb : d266246 q = 1) : d201987 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4342, d201987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4342, d201987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4343 q = 1) (hb : d266246 q = 1) : d201988 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4343, d201988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4343, d201988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4349 q = 1) (hb : d266246 q = 1) : d201989 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4349, d201989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4349, d201989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72833 (p : Pattern) (ha : d231 p = 1) (hb : d266246 p = 1) : d25153 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d226 q = 1) (hb : d266246 q = 1) : d25148 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d25148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d25148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72828 q ha hb
  have h2 (q : Pattern) (ha : d139 q = 1) (hb : d266246 q = 1) : d25105 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d25105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72828 q ha hb
    | true =>
      simp only [d139, d25105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d227 q = 1) (hb : d266246 q = 1) : d25149 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d25149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d227, d25149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d140 q = 1) (hb : d266246 q = 1) : d25106 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d25106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d140, d25106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d228 q = 1) (hb : d266246 q = 1) : d25150 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d25150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d228, d25150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d229 q = 1) (hb : d266246 q = 1) : d25151 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d25151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d229, d25151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d266246 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d230 q = 1) (hb : d266246 q = 1) : d25152 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d230, d25152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d230, d25152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d266246 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d231 q = 1) (hb : d266246 q = 1) : d25153 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231, d25153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d231, d25153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro72834 (p : Pattern) (ha : d237 p = 1) (hb : d266246 p = 1) : d25159 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d266246 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d232 q = 1) (hb : d266246 q = 1) : d25154 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d25154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72833 q ha hb
    | true =>
      simp only [d232, d25154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d233 q = 1) (hb : d266246 q = 1) : d25155 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d25155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d25155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234 q = 1) (hb : d266246 q = 1) : d25156 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d25156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d25156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d266246 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d235 q = 1) (hb : d266246 q = 1) : d25157 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d25157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d235, d25157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d266246 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d236 q = 1) (hb : d266246 q = 1) : d25158 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d236, d25158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d236, d25158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237 q = 1) (hb : d266246 q = 1) : d25159 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237, d25159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237, d25159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro72835 (p : Pattern) (ha : d243 p = 1) (hb : d266246 p = 1) : d25165 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d266246 q = 1) : d25160 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d25160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72834 q ha hb
    | true =>
      simp only [d238, d25160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d266246 q = 1) : d25161 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d25161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d25161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d266246 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d240 q = 1) (hb : d266246 q = 1) : d25162 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d240, d25162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d240, d25162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d241 q = 1) (hb : d266246 q = 1) : d25163 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d241, d25163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d241, d25163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d242 q = 1) (hb : d266246 q = 1) : d25164 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d242, d25164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d242, d25164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d243 q = 1) (hb : d266246 q = 1) : d25165 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243, d25165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243, d25165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro72836 (p : Pattern) (ha : d4359 p = 1) (hb : d266246 p = 1) : d201999 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d266246 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d244 q = 1) (hb : d266246 q = 1) : d25166 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d25166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72835 q ha hb
    | true =>
      simp only [d244, d25166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4355 q = 1) (hb : d266246 q = 1) : d201995 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4355, d201995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4355, d201995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d266246 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4356 q = 1) (hb : d266246 q = 1) : d201996 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4356, d201996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4356, d201996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4357 q = 1) (hb : d266246 q = 1) : d201997 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4357, d201997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4357, d201997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4358 q = 1) (hb : d266246 q = 1) : d201998 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4358, d201998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4358, d201998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4359 q = 1) (hb : d266246 q = 1) : d201999 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4359, d201999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4359, d201999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72837 (p : Pattern) (ha : d156 p = 1) (hb : d266246 p = 1) : d25122 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d266246 q = 1) : d25117 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d25117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72830 q ha hb
    | true =>
      simp only [d151, d25117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d266246 q = 1) : d25118 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d25118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d25118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d266246 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d266246 q = 1) : d25119 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d25119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d25119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d266246 q = 1) : d25120 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d25120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d25120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d155 q = 1) (hb : d266246 q = 1) : d25121 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d25121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155, d25121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d156 q = 1) (hb : d266246 q = 1) : d25122 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156, d25122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156, d25122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro72838 (p : Pattern) (ha : d51643 p = 1) (hb : d266246 p = 1) : d201977 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d266246 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d266246 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d266246 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d157 q = 1) (hb : d266246 q = 1) : d25123 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d25123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72837 q ha hb
    | true =>
      simp only [d157, d25123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4335 q = 1) (hb : d266246 q = 1) : d201973 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d201973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4335, d201973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d266246 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4336 q = 1) (hb : d266246 q = 1) : d201974 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d201974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4336, d201974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51641 q = 1) (hb : d266246 q = 1) : d201975 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d201975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51641, d201975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51642 q = 1) (hb : d266246 q = 1) : d201976 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d201976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51642, d201976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d51643 q = 1) (hb : d266246 q = 1) : d201977 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51643, d201977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51643, d201977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro72839 (p : Pattern) (ha : d51646 p = 1) (hb : d266246 p = 1) : d201982 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d266246 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d266246 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d266246 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d157 q = 1) (hb : d266246 q = 1) : d25123 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d25123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72837 q ha hb
    | true =>
      simp only [d157, d25123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4335 q = 1) (hb : d266246 q = 1) : d201973 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d201973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4335, d201973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d266246 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4336 q = 1) (hb : d266246 q = 1) : d201974 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d201974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4336, d201974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51641 q = 1) (hb : d266246 q = 1) : d201975 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d201975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51641, d201975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51642 q = 1) (hb : d266246 q = 1) : d201976 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d201976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51642, d201976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d266246 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d266246 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d266246 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d204 q = 1) (hb : d266246 q = 1) : d25130 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d25130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72831 q ha hb
    | true =>
      simp only [d204, d25130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d4340 q = 1) (hb : d266246 q = 1) : d201978 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d201978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4340, d201978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d266246 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d4341 q = 1) (hb : d266246 q = 1) : d201979 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d201979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4341, d201979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51644 q = 1) (hb : d266246 q = 1) : d201980 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51644, d201980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51644, d201980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d51645 q = 1) (hb : d266246 q = 1) : d201981 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51645, d201981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51645, d201981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d51646 q = 1) (hb : d266246 q = 1) : d201982 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51646, d201982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51646, d201982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro72840 (p : Pattern) (ha : d51652 p = 1) (hb : d266246 p = 1) : d202005 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d266246 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51647 q = 1) (hb : d266246 q = 1) : d201983 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51647, d201983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72838 q ha hb
    | true =>
      simp only [d51647, d201983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72839 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d266246 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51648 q = 1) (hb : d266246 q = 1) : d201984 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51648, d201984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51648, d201984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51649 q = 1) (hb : d266246 q = 1) : d201985 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51649, d201985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51649, d201985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51650 q = 1) (hb : d266246 q = 1) : d201986 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51650, d201986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51650, d201986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4350 q = 1) (hb : d266246 q = 1) : d201990 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4350, d201990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4350, d201990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72832 q ha hb
  have h8 (q : Pattern) (ha : d4351 q = 1) (hb : d266246 q = 1) : d201991 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4351, d201991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4351, d201991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d4352 q = 1) (hb : d266246 q = 1) : d201992 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4352, d201992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4352, d201992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d4353 q = 1) (hb : d266246 q = 1) : d201993 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4353, d201993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4353, d201993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d51651 q = 1) (hb : d266246 q = 1) : d201994 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51651, d201994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51651, d201994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4360 q = 1) (hb : d266246 q = 1) : d202000 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4360, d202000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4360, d202000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72836 q ha hb
  have h13 (q : Pattern) (ha : d4361 q = 1) (hb : d266246 q = 1) : d202001 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4361, d202001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4361, d202001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d4362 q = 1) (hb : d266246 q = 1) : d202002 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4362, d202002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4362, d202002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d4363 q = 1) (hb : d266246 q = 1) : d202003 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4363, d202003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4363, d202003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d4364 q = 1) (hb : d266246 q = 1) : d202004 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4364, d202004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4364, d202004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d51652 q = 1) (hb : d266246 q = 1) : d202005 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51652, d202005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51652, d202005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro72841 (p : Pattern) (ha : d284 p = 1) (hb : d266246 p = 1) : d25187 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d266246 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d266246 q = 1) : d25123 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d25123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72837 q ha hb
    | true =>
      simp only [d157, d25123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d266246 q = 1) : d25183 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d25183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d25183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d266246 q = 1) : d25184 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d25184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d25184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d266246 q = 1) : d25185 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d25185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d25185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d266246 q = 1) : d25186 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d25186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d25186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d284 q = 1) (hb : d266246 q = 1) : d25187 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d284, d25187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d284, d25187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro72842 (p : Pattern) (ha : d291 p = 1) (hb : d266246 p = 1) : d25194 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d266246 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d266246 q = 1) : d25123 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d25123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72837 q ha hb
    | true =>
      simp only [d157, d25123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d266246 q = 1) : d25183 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d25183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d25183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d266246 q = 1) : d25184 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d25184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d25184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d266246 q = 1) : d25185 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d25185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d25185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d266246 q = 1) : d25186 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d25186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d25186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d266246 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d204 q = 1) (hb : d266246 q = 1) : d25130 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d25130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72831 q ha hb
    | true =>
      simp only [d204, d25130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d287 q = 1) (hb : d266246 q = 1) : d25190 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d25190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, d25190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d288 q = 1) (hb : d266246 q = 1) : d25191 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d25191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d288, d25191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d289 q = 1) (hb : d266246 q = 1) : d25192 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d25192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d25192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d290 q = 1) (hb : d266246 q = 1) : d25193 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d25193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d25193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d291 q = 1) (hb : d266246 q = 1) : d25194 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291, d25194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d291, d25194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro72843 (p : Pattern) (ha : d397 p = 1) (hb : d266246 p = 1) : d25296 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d266246 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d266246 q = 1) : d25123 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d25123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72837 q ha hb
    | true =>
      simp only [d157, d25123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d266246 q = 1) : d25183 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d25183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d25183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d266246 q = 1) : d25184 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d25184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d25184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d266246 q = 1) : d25185 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d25185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d25185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d266246 q = 1) : d25186 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d25186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d25186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d266246 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d397 q = 1) (hb : d266246 q = 1) : d25296 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d397, d25296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d397, d25296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72844 (p : Pattern) (ha : d296 p = 1) (hb : d266246 p = 1) : d25199 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d266246 q = 1) : d25117 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d25117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72830 q ha hb
    | true =>
      simp only [d151, d25117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d266246 q = 1) : d25118 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d25118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d25118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d266246 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d266246 q = 1) : d25119 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d25119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d25119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d266246 q = 1) : d25120 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d25120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d25120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d295 q = 1) (hb : d266246 q = 1) : d25198 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, d25198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295, d25198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d296 q = 1) (hb : d266246 q = 1) : d25199 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d296, d25199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d296, d25199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro72845 (p : Pattern) (ha : d303 p = 1) (hb : d266246 p = 1) : d25206 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d266246 q = 1) : d25117 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d25117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72830 q ha hb
    | true =>
      simp only [d151, d25117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d266246 q = 1) : d25118 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d25118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d25118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d266246 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d266246 q = 1) : d25119 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d25119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d25119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d301 q = 1) (hb : d266246 q = 1) : d25204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d25204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d301, d25204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d302 q = 1) (hb : d266246 q = 1) : d25205 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, d25205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d302, d25205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d303 q = 1) (hb : d266246 q = 1) : d25206 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d303, d25206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d303, d25206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro72846 (p : Pattern) (ha : d4736 p = 1) (hb : d266246 p = 1) : d25267 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d266246 q = 1) : d25117 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d25117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72830 q ha hb
    | true =>
      simp only [d151, d25117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d266246 q = 1) : d25118 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d25118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d25118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4733 q = 1) (hb : d266246 q = 1) : d25264 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d25264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, d25264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4734 q = 1) (hb : d266246 q = 1) : d25265 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d25265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4734, d25265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4735 q = 1) (hb : d266246 q = 1) : d25266 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d25266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4735, d25266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4736 q = 1) (hb : d266246 q = 1) : d25267 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d4736, d25267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4736, d25267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72847 (p : Pattern) (ha : d318 p = 1) (hb : d266246 p = 1) : d266247 p = 1 := by
  have h0 (q : Pattern) (ha : d314 q = 1) (hb : d236581 q = 1) : d314 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d134 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d315 q = 1) (hb : d266244 q = 1) : d25210 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d266244, d25210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d315, d266244, d25210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d133 q = 1) (hb : d241830 q = 1) : d25433 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d241830, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47928 q ha hb
    | true =>
      simp only [d133, d241830, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d134 q = 1) (hb : d241830 q = 1) : d25434 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d20 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d135 q = 1) (hb : d266245 q = 1) : d25435 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d266245, d25435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d135, d266245, d25435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d316 q = 1) (hb : d266246 q = 1) : d25436 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d316, d266246, d25436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d316, d266246, d25436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d317 q = 1) (hb : d266246 q = 1) : d25437 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d317, d25437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d317, d25437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d134 q = 1) (hb : d236581 q = 1) : d134 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d135 q = 1) (hb : d266244 q = 1) : d9796 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d266244, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d135, d266244, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h14 (q : Pattern) (ha : d21 q = 1) (hb : d266245 q = 1) : d21 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d136 q = 1) (hb : d266246 q = 1) : d25102 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d136, d266246, d25102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d136, d266246, d25102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d137 q = 1) (hb : d266246 q = 1) : d25103 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d137, d25103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d137, d25103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h17 (q : Pattern) (ha : d318 q = 1) (hb : d266246 q = 1) : d266247 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d318, d266247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d318, d266247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro72848 (p : Pattern) (ha : d9381 p = 1) (hb : d266246 p = 1) : d25221 p = 1 := by
  have h0 (q : Pattern) (ha : d134 q = 1) (hb : d236581 q = 1) : d134 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d135 q = 1) (hb : d266244 q = 1) : d9796 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d266244, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d135, d266244, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d266245 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5448 q = 1) (hb : d266246 q = 1) : d25219 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5448, d266246, d25219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5448, d266246, d25219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5449 q = 1) (hb : d266246 q = 1) : d25220 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5449, d25220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5449, d25220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23 q = 1) (hb : d266246 q = 1) : d23 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9381 q = 1) (hb : d266246 q = 1) : d25221 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9381, d25221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9381, d25221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72849 (p : Pattern) (ha : d15966 p = 1) (hb : d266246 p = 1) : d266253 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d266246 q = 1) : d266248 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d266248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72847 q ha hb
    | true =>
      simp only [d319, d266248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d320 q = 1) (hb : d266246 q = 1) : d266249 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d266249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320, d266249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321 q = 1) (hb : d266246 q = 1) : d266250 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d266250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d266250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d266246 q = 1) : d266251 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d266251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322, d266251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d139 q = 1) (hb : d266246 q = 1) : d25105 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d25105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72828 q ha hb
    | true =>
      simp only [d139, d25105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d140 q = 1) (hb : d266246 q = 1) : d25106 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d25106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d140, d25106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d141 q = 1) (hb : d266246 q = 1) : d25107 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d25107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d25107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d142 q = 1) (hb : d266246 q = 1) : d25108 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d25108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d142, d25108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d323 q = 1) (hb : d266246 q = 1) : d266252 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d323, d266252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d323, d266252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9382 q = 1) (hb : d266246 q = 1) : d25222 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72848 q ha hb
    | true =>
      simp only [d9382, d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9384 q = 1) (hb : d266246 q = 1) : d25223 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9384, d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12493 q = 1) (hb : d266246 q = 1) : d25224 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d25224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d25224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12494 q = 1) (hb : d266246 q = 1) : d25225 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d25225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12494, d25225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d28 q = 1) (hb : d266246 q = 1) : d28 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d12495 q = 1) (hb : d266246 q = 1) : d25226 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12495, d25226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12495, d25226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15966 q = 1) (hb : d266246 q = 1) : d266253 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15966, d266253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15966, d266253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro72850 (p : Pattern) (ha : d15972 p = 1) (hb : d266246 p = 1) : d266259 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15967 q = 1) (hb : d266246 q = 1) : d266254 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d266254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72849 q ha hb
    | true =>
      simp only [d15967, d266254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72829 q ha hb
  have h2 (q : Pattern) (ha : d15968 q = 1) (hb : d266246 q = 1) : d266255 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d266255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d266255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15969 q = 1) (hb : d266246 q = 1) : d266256 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d266256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d266256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d266246 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d145 q = 1) (hb : d266246 q = 1) : d25111 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d25111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72829 q ha hb
    | true =>
      simp only [d145, d25111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146 q = 1) (hb : d266246 q = 1) : d25112 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d25112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d25112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147 q = 1) (hb : d266246 q = 1) : d25113 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d25113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d25113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15970 q = 1) (hb : d266246 q = 1) : d266257 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d266257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15970, d266257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d266246 q = 1) : d33 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d148 q = 1) (hb : d266246 q = 1) : d25114 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d25114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148, d25114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15971 q = 1) (hb : d266246 q = 1) : d266258 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15971, d266258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15971, d266258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15972 q = 1) (hb : d266246 q = 1) : d266259 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15972, d266259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15972, d266259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro72851 (p : Pattern) (ha : d15978 p = 1) (hb : d266246 p = 1) : d266265 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15973 q = 1) (hb : d266246 q = 1) : d266260 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15973, d266260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72850 q ha hb
    | true =>
      simp only [d15973, d266260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15974 q = 1) (hb : d266246 q = 1) : d266261 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15974, d266261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15974, d266261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d151 q = 1) (hb : d266246 q = 1) : d25117 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d25117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72830 q ha hb
    | true =>
      simp only [d151, d25117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d266246 q = 1) : d25118 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d25118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d25118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15975 q = 1) (hb : d266246 q = 1) : d266262 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15975, d266262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15975, d266262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15976 q = 1) (hb : d266246 q = 1) : d266263 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15976, d266263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15976, d266263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15977 q = 1) (hb : d266246 q = 1) : d266264 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15977, d266264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15977, d266264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15978 q = 1) (hb : d266246 q = 1) : d266265 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15978, d266265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15978, d266265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72852 (p : Pattern) (ha : d128195 p = 1) (hb : d266246 p = 1) : d266271 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d266246 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d297 q = 1) (hb : d266246 q = 1) : d25200 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d25200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72844 q ha hb
    | true =>
      simp only [d297, d25200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d298 q = 1) (hb : d266246 q = 1) : d25201 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d25201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d25201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d299 q = 1) (hb : d266246 q = 1) : d25202 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d25202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d299, d25202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d300 q = 1) (hb : d266246 q = 1) : d25203 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d25203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d25203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d266246 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d304 q = 1) (hb : d266246 q = 1) : d25207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d25207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72845 q ha hb
    | true =>
      simp only [d304, d25207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305 q = 1) (hb : d266246 q = 1) : d25208 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d25208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d25208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306 q = 1) (hb : d266246 q = 1) : d25209 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d25209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306, d25209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15979 q = 1) (hb : d266246 q = 1) : d266266 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15979, d266266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72851 q ha hb
    | true =>
      simp only [d15979, d266266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72837 q ha hb
  have h11 (q : Pattern) (ha : d128191 q = 1) (hb : d266246 q = 1) : d266267 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128191, d266267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128191, d266267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4737 q = 1) (hb : d266246 q = 1) : d25268 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d25268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72846 q ha hb
    | true =>
      simp only [d4737, d25268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5350 q = 1) (hb : d266246 q = 1) : d25269 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d25269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5350, d25269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d128192 q = 1) (hb : d266246 q = 1) : d266268 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128192, d266268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128192, d266268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128193 q = 1) (hb : d266246 q = 1) : d266269 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128193, d266269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128193, d266269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128194 q = 1) (hb : d266246 q = 1) : d266270 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128194, d266270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128194, d266270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128195 q = 1) (hb : d266246 q = 1) : d266271 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128195, d266271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128195, d266271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro72853 (p : Pattern) (ha : d376 p = 1) (hb : d266246 p = 1) : d25274 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d266246 q = 1) : d25117 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d25117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72830 q ha hb
    | true =>
      simp only [d151, d25117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d266246 q = 1) : d25118 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d25118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d25118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d266246 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d266246 q = 1) : d25119 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d25119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d25119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d266246 q = 1) : d25120 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d25120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d25120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d295 q = 1) (hb : d266246 q = 1) : d25198 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, d25198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295, d25198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d376 q = 1) (hb : d266246 q = 1) : d25274 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376, d25274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d376, d25274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro72854 (p : Pattern) (ha : d381 p = 1) (hb : d266246 p = 1) : d25279 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d266246 q = 1) : d25117 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d25117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72830 q ha hb
    | true =>
      simp only [d151, d25117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d266246 q = 1) : d25118 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d25118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d25118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d266246 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d266246 q = 1) : d25119 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d25119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d25119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d301 q = 1) (hb : d266246 q = 1) : d25204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d25204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d301, d25204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d302 q = 1) (hb : d266246 q = 1) : d25205 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, d25205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d302, d25205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d381 q = 1) (hb : d266246 q = 1) : d25279 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d381, d25279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d381, d25279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro72855 (p : Pattern) (ha : d5355 p = 1) (hb : d266246 p = 1) : d25288 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d266246 q = 1) : d25117 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d25117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72830 q ha hb
    | true =>
      simp only [d151, d25117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d266246 q = 1) : d25118 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d25118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d25118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4733 q = 1) (hb : d266246 q = 1) : d25264 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d25264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, d25264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4734 q = 1) (hb : d266246 q = 1) : d25265 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d25265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4734, d25265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4735 q = 1) (hb : d266246 q = 1) : d25266 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d25266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4735, d25266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5355 q = 1) (hb : d266246 q = 1) : d25288 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5355, d25288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5355, d25288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72856 (p : Pattern) (ha : d15985 p = 1) (hb : d266246 p = 1) : d266272 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15973 q = 1) (hb : d266246 q = 1) : d266260 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15973, d266260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72850 q ha hb
    | true =>
      simp only [d15973, d266260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15974 q = 1) (hb : d266246 q = 1) : d266261 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15974, d266261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15974, d266261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d151 q = 1) (hb : d266246 q = 1) : d25117 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d25117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72830 q ha hb
    | true =>
      simp only [d151, d25117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d266246 q = 1) : d25118 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d25118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d25118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15975 q = 1) (hb : d266246 q = 1) : d266262 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15975, d266262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15975, d266262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15976 q = 1) (hb : d266246 q = 1) : d266263 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15976, d266263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15976, d266263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15977 q = 1) (hb : d266246 q = 1) : d266264 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15977, d266264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15977, d266264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15985 q = 1) (hb : d266246 q = 1) : d266272 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15985, d266272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15985, d266272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro72857 (p : Pattern) (ha : d128200 p = 1) (hb : d266246 p = 1) : d266278 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d266246 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d297 q = 1) (hb : d266246 q = 1) : d25200 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d25200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72844 q ha hb
    | true =>
      simp only [d297, d25200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d298 q = 1) (hb : d266246 q = 1) : d25201 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d25201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d25201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d299 q = 1) (hb : d266246 q = 1) : d25202 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d25202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d299, d25202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d300 q = 1) (hb : d266246 q = 1) : d25203 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d25203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d25203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d266246 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d304 q = 1) (hb : d266246 q = 1) : d25207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d25207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72845 q ha hb
    | true =>
      simp only [d304, d25207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305 q = 1) (hb : d266246 q = 1) : d25208 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d25208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d25208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306 q = 1) (hb : d266246 q = 1) : d25209 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d25209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306, d25209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15979 q = 1) (hb : d266246 q = 1) : d266266 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15979, d266266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72851 q ha hb
    | true =>
      simp only [d15979, d266266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72837 q ha hb
  have h11 (q : Pattern) (ha : d128191 q = 1) (hb : d266246 q = 1) : d266267 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128191, d266267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128191, d266267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4737 q = 1) (hb : d266246 q = 1) : d25268 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d25268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72846 q ha hb
    | true =>
      simp only [d4737, d25268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5350 q = 1) (hb : d266246 q = 1) : d25269 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d25269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5350, d25269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d128192 q = 1) (hb : d266246 q = 1) : d266268 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128192, d266268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128192, d266268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128193 q = 1) (hb : d266246 q = 1) : d266269 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128193, d266269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128193, d266269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128194 q = 1) (hb : d266246 q = 1) : d266270 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128194, d266270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128194, d266270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d266246 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d377 q = 1) (hb : d266246 q = 1) : d25275 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377, d25275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72853 q ha hb
    | true =>
      simp only [d377, d25275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d378 q = 1) (hb : d266246 q = 1) : d25276 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d378, d25276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d378, d25276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d379 q = 1) (hb : d266246 q = 1) : d25277 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d379, d25277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d379, d25277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d380 q = 1) (hb : d266246 q = 1) : d25278 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d380, d25278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d380, d25278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d266246 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d382 q = 1) (hb : d266246 q = 1) : d25280 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d382, d25280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72854 q ha hb
    | true =>
      simp only [d382, d25280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d383 q = 1) (hb : d266246 q = 1) : d25281 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d383, d25281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d383, d25281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d384 q = 1) (hb : d266246 q = 1) : d25282 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d384, d25282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d384, d25282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d15986 q = 1) (hb : d266246 q = 1) : d266273 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15986, d266273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72856 q ha hb
    | true =>
      simp only [d15986, d266273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72831 q ha hb
  have h27 (q : Pattern) (ha : d128196 q = 1) (hb : d266246 q = 1) : d266274 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128196, d266274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d128196, d266274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d5356 q = 1) (hb : d266246 q = 1) : d25289 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d25289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72855 q ha hb
    | true =>
      simp only [d5356, d25289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d5357 q = 1) (hb : d266246 q = 1) : d25290 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d25290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d5357, d25290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d128197 q = 1) (hb : d266246 q = 1) : d266275 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128197, d266275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d128197, d266275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d128198 q = 1) (hb : d266246 q = 1) : d266276 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128198, d266276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d128198, d266276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d128199 q = 1) (hb : d266246 q = 1) : d266277 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128199, d266277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128199, d266277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d128200 q = 1) (hb : d266246 q = 1) : d266278 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128200, d266278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128200, d266278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro72858 (p : Pattern) (ha : d128207 p = 1) (hb : d266246 p = 1) : d266285 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15986 q = 1) (hb : d266246 q = 1) : d266273 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15986, d266273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72856 q ha hb
    | true =>
      simp only [d15986, d266273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72831 q ha hb
  have h2 (q : Pattern) (ha : d128196 q = 1) (hb : d266246 q = 1) : d266274 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128196, d266274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128196, d266274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5356 q = 1) (hb : d266246 q = 1) : d25289 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d25289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72855 q ha hb
    | true =>
      simp only [d5356, d25289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5357 q = 1) (hb : d266246 q = 1) : d25290 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d25290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5357, d25290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128197 q = 1) (hb : d266246 q = 1) : d266275 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128197, d266275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128197, d266275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128205 q = 1) (hb : d266246 q = 1) : d266283 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128205, d266283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128205, d266283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128206 q = 1) (hb : d266246 q = 1) : d266284 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128206, d266284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128206, d266284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128207 q = 1) (hb : d266246 q = 1) : d266285 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128207, d266285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128207, d266285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72859 (p : Pattern) (ha : d5377 p = 1) (hb : d266246 p = 1) : d25356 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d266246 q = 1) : d25160 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d25160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72834 q ha hb
    | true =>
      simp only [d238, d25160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d266246 q = 1) : d25161 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d25161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d25161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5374 q = 1) (hb : d266246 q = 1) : d25353 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5374, d25353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5374, d25353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5375 q = 1) (hb : d266246 q = 1) : d25354 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5375, d25354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5375, d25354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5376 q = 1) (hb : d266246 q = 1) : d25355 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5376, d25355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5376, d25355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5377 q = 1) (hb : d266246 q = 1) : d25356 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5377, d25356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5377, d25356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72860 (p : Pattern) (ha : d16004 p = 1) (hb : d266246 p = 1) : d266296 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d412 q = 1) (hb : d266246 q = 1) : d266291 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d266291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d266291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72847 q ha hb
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d266246 q = 1) : d266248 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d266248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72847 q ha hb
    | true =>
      simp only [d319, d266248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d413 q = 1) (hb : d266246 q = 1) : d266292 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d266292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d413, d266292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320 q = 1) (hb : d266246 q = 1) : d266249 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d266249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d266249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d414 q = 1) (hb : d266246 q = 1) : d266293 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d266293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d414, d266293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d415 q = 1) (hb : d266246 q = 1) : d266294 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d266294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d415, d266294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d226 q = 1) (hb : d266246 q = 1) : d25148 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d25148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d25148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72828 q ha hb
  have h8 (q : Pattern) (ha : d139 q = 1) (hb : d266246 q = 1) : d25105 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d25105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72828 q ha hb
    | true =>
      simp only [d139, d25105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d227 q = 1) (hb : d266246 q = 1) : d25149 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d25149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d227, d25149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d140 q = 1) (hb : d266246 q = 1) : d25106 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d25106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d140, d25106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d228 q = 1) (hb : d266246 q = 1) : d25150 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d25150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d228, d25150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d229 q = 1) (hb : d266246 q = 1) : d25151 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d25151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d229, d25151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d416 q = 1) (hb : d266246 q = 1) : d266295 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d416, d266295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d416, d266295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12599 q = 1) (hb : d266246 q = 1) : d25314 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d25314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d25314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72848 q ha hb
  have h15 (q : Pattern) (ha : d9382 q = 1) (hb : d266246 q = 1) : d25222 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72848 q ha hb
    | true =>
      simp only [d9382, d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d12600 q = 1) (hb : d266246 q = 1) : d25315 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d25315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d12600, d25315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9384 q = 1) (hb : d266246 q = 1) : d25223 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9384, d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12601 q = 1) (hb : d266246 q = 1) : d25316 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d25316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12601, d25316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12602 q = 1) (hb : d266246 q = 1) : d25317 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d25317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d12602, d25317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d69 q = 1) (hb : d266246 q = 1) : d69 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d12603 q = 1) (hb : d266246 q = 1) : d25318 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12603, d25318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d12603, d25318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d16004 q = 1) (hb : d266246 q = 1) : d266296 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16004, d266296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16004, d266296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro72861 (p : Pattern) (ha : d16010 p = 1) (hb : d266246 p = 1) : d266302 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16005 q = 1) (hb : d266246 q = 1) : d266297 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d266297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72860 q ha hb
    | true =>
      simp only [d16005, d266297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72833 q ha hb
  have h2 (q : Pattern) (ha : d16006 q = 1) (hb : d266246 q = 1) : d266298 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d266298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d266298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16007 q = 1) (hb : d266246 q = 1) : d266299 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d266299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d266299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d266246 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d232 q = 1) (hb : d266246 q = 1) : d25154 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d25154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72833 q ha hb
    | true =>
      simp only [d232, d25154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d233 q = 1) (hb : d266246 q = 1) : d25155 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d25155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d25155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234 q = 1) (hb : d266246 q = 1) : d25156 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d25156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d25156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16008 q = 1) (hb : d266246 q = 1) : d266300 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d266300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16008, d266300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74 q = 1) (hb : d266246 q = 1) : d74 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d235 q = 1) (hb : d266246 q = 1) : d25157 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d25157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d235, d25157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16009 q = 1) (hb : d266246 q = 1) : d266301 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16009, d266301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16009, d266301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16010 q = 1) (hb : d266246 q = 1) : d266302 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16010, d266302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16010, d266302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro72862 (p : Pattern) (ha : d16016 p = 1) (hb : d266246 p = 1) : d266308 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16011 q = 1) (hb : d266246 q = 1) : d266303 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16011, d266303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72861 q ha hb
    | true =>
      simp only [d16011, d266303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16012 q = 1) (hb : d266246 q = 1) : d266304 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16012, d266304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16012, d266304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d238 q = 1) (hb : d266246 q = 1) : d25160 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d25160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72834 q ha hb
    | true =>
      simp only [d238, d25160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d239 q = 1) (hb : d266246 q = 1) : d25161 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d25161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d25161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16013 q = 1) (hb : d266246 q = 1) : d266305 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16013, d266305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16013, d266305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16014 q = 1) (hb : d266246 q = 1) : d266306 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16014, d266306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16014, d266306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16015 q = 1) (hb : d266246 q = 1) : d266307 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16015, d266307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16015, d266307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16016 q = 1) (hb : d266246 q = 1) : d266308 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16016, d266308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16016, d266308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro72863 (p : Pattern) (ha : d128217 p = 1) (hb : d266246 p = 1) : d266314 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16017 q = 1) (hb : d266246 q = 1) : d266309 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16017, d266309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72862 q ha hb
    | true =>
      simp only [d16017, d266309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72835 q ha hb
  have h2 (q : Pattern) (ha : d128213 q = 1) (hb : d266246 q = 1) : d266310 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128213, d266310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128213, d266310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5378 q = 1) (hb : d266246 q = 1) : d25357 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5378, d25357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72859 q ha hb
    | true =>
      simp only [d5378, d25357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5379 q = 1) (hb : d266246 q = 1) : d25358 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5379, d25358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5379, d25358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128214 q = 1) (hb : d266246 q = 1) : d266311 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128214, d266311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128214, d266311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128215 q = 1) (hb : d266246 q = 1) : d266312 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128215, d266312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128215, d266312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128216 q = 1) (hb : d266246 q = 1) : d266313 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128216, d266313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128216, d266313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128217 q = 1) (hb : d266246 q = 1) : d266314 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128217, d266314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128217, d266314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72864 (p : Pattern) (ha : d128223 p = 1) (hb : d266246 p = 1) : d266320 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d266246 q = 1) : d25188 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, d25188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, d25188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72841 q ha hb
  have h2 (q : Pattern) (ha : d286 q = 1) (hb : d266246 q = 1) : d25189 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, d25189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, d25189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d292 q = 1) (hb : d266246 q = 1) : d25195 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d25195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72841 q ha hb
    | true =>
      simp only [d292, d25195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72842 q ha hb
  have h4 (q : Pattern) (ha : d293 q = 1) (hb : d266246 q = 1) : d25196 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d25196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293, d25196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d294 q = 1) (hb : d266246 q = 1) : d25197 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, d25197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d294, d25197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128201 q = 1) (hb : d266246 q = 1) : d266279 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128201, d266279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72852 q ha hb
    | true =>
      simp only [d128201, d266279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72857 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d266246 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d398 q = 1) (hb : d266246 q = 1) : d25297 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d398, d25297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72843 q ha hb
    | true =>
      simp only [d398, d25297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128202 q = 1) (hb : d266246 q = 1) : d266280 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128202, d266280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128202, d266280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128203 q = 1) (hb : d266246 q = 1) : d266281 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128203, d266281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128203, d266281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d128204 q = 1) (hb : d266246 q = 1) : d266282 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128204, d266282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128204, d266282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d128208 q = 1) (hb : d266246 q = 1) : d266286 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128208, d266286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128208, d266286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72858 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d266246 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d128209 q = 1) (hb : d266246 q = 1) : d266287 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128209, d266287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128209, d266287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128210 q = 1) (hb : d266246 q = 1) : d266288 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128210, d266288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128210, d266288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d128211 q = 1) (hb : d266246 q = 1) : d266289 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128211, d266289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128211, d266289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d128212 q = 1) (hb : d266246 q = 1) : d266290 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128212, d266290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128212, d266290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d128218 q = 1) (hb : d266246 q = 1) : d266315 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128218, d266315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128218, d266315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72863 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d266246 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d128219 q = 1) (hb : d266246 q = 1) : d266316 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128219, d266316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128219, d266316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d128220 q = 1) (hb : d266246 q = 1) : d266317 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128220, d266317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128220, d266317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d128221 q = 1) (hb : d266246 q = 1) : d266318 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128221, d266318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128221, d266318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d128222 q = 1) (hb : d266246 q = 1) : d266319 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128222, d266319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128222, d266319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d128223 q = 1) (hb : d266246 q = 1) : d266320 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128223, d266320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128223, d266320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro72865 (p : Pattern) (ha : d128229 p = 1) (hb : d266246 p = 1) : d266326 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d266246 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51653 q = 1) (hb : d266246 q = 1) : d202006 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51653, d202006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51653, d202006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72840 q ha hb
  have h3 (q : Pattern) (ha : d51654 q = 1) (hb : d266246 q = 1) : d202007 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51654, d202007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51654, d202007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51655 q = 1) (hb : d266246 q = 1) : d202008 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51655, d202008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51655, d202008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51656 q = 1) (hb : d266246 q = 1) : d202009 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51656, d202009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51656, d202009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51657 q = 1) (hb : d266246 q = 1) : d202010 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51657, d202010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51657, d202010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128224 q = 1) (hb : d266246 q = 1) : d266321 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128224, d266321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128224, d266321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72864 q ha hb
  have h8 (q : Pattern) (ha : d128225 q = 1) (hb : d266246 q = 1) : d266322 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128225, d266322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128225, d266322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128226 q = 1) (hb : d266246 q = 1) : d266323 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128226, d266323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128226, d266323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128227 q = 1) (hb : d266246 q = 1) : d266324 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128227, d266324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128227, d266324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128228 q = 1) (hb : d266246 q = 1) : d266325 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128228, d266325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128228, d266325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d128229 q = 1) (hb : d266246 q = 1) : d266326 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128229, d266326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128229, d266326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro72866 (p : Pattern) (ha : d481 p = 1) (hb : d266246 p = 1) : d25381 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d266246 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145 q = 1) (hb : d266246 q = 1) : d25111 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d25111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72829 q ha hb
    | true =>
      simp only [d145, d25111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146 q = 1) (hb : d266246 q = 1) : d25112 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d25112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d25112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147 q = 1) (hb : d266246 q = 1) : d25113 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d25113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d25113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d475 q = 1) (hb : d266246 q = 1) : d25375 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d25375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d475, d25375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d480 q = 1) (hb : d266246 q = 1) : d25380 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d480, d25380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d480, d25380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d481 q = 1) (hb : d266246 q = 1) : d25381 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d481, d25381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d481, d25381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro72867 (p : Pattern) (ha : d491 p = 1) (hb : d266246 p = 1) : d25391 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d266246 q = 1) : d25382 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d25382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72866 q ha hb
    | true =>
      simp only [d482, d25382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d266246 q = 1) : d25383 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d25383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d25383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d266246 q = 1) : d25388 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d25388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d25388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d266246 q = 1) : d25389 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d25389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d25389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d266246 q = 1) : d25390 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d25390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d25390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d491 q = 1) (hb : d266246 q = 1) : d25391 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d491, d25391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d491, d25391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72868 (p : Pattern) (ha : d501 p = 1) (hb : d266246 p = 1) : d25401 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d266246 q = 1) : d25382 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d25382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72866 q ha hb
    | true =>
      simp only [d482, d25382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d266246 q = 1) : d25383 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d25383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d25383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d266246 q = 1) : d25388 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d25388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d25388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d266246 q = 1) : d25389 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d25389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d25389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d266246 q = 1) : d25390 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d25390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d25390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d501 q = 1) (hb : d266246 q = 1) : d25401 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d501, d25401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d501, d25401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72869 (p : Pattern) (ha : d644 p = 1) (hb : d266246 p = 1) : d25562 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d633 q = 1) (hb : d266246 q = 1) : d25551 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d25551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72867 q ha hb
    | true =>
      simp only [d633, d25551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d634 q = 1) (hb : d266246 q = 1) : d25552 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d25552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d25552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d635 q = 1) (hb : d266246 q = 1) : d25553 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d25553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d635, d25553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d636 q = 1) (hb : d266246 q = 1) : d25554 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d25554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d25554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d637 q = 1) (hb : d266246 q = 1) : d25555 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d25555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d25555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d639 q = 1) (hb : d266246 q = 1) : d25557 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d25557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72868 q ha hb
    | true =>
      simp only [d639, d25557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d640 q = 1) (hb : d266246 q = 1) : d25558 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d25558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, d25558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d641 q = 1) (hb : d266246 q = 1) : d25559 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d25559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d641, d25559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d642 q = 1) (hb : d266246 q = 1) : d25560 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d25560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, d25560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d643 q = 1) (hb : d266246 q = 1) : d25561 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d25561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d25561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d644 q = 1) (hb : d266246 q = 1) : d25562 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d644, d25562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d644, d25562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro72870 (p : Pattern) (ha : d653 p = 1) (hb : d266246 p = 1) : d25571 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d639 q = 1) (hb : d266246 q = 1) : d25557 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d25557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72868 q ha hb
    | true =>
      simp only [d639, d25557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d640 q = 1) (hb : d266246 q = 1) : d25558 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d25558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, d25558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d641 q = 1) (hb : d266246 q = 1) : d25559 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d25559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d641, d25559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d642 q = 1) (hb : d266246 q = 1) : d25560 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d25560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, d25560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d643 q = 1) (hb : d266246 q = 1) : d25561 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d25561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d25561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d653 q = 1) (hb : d266246 q = 1) : d25571 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d653, d25571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d653, d25571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72871 (p : Pattern) (ha : d683 p = 1) (hb : d266246 p = 1) : d25614 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d266246 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d232 q = 1) (hb : d266246 q = 1) : d25154 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d25154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72833 q ha hb
    | true =>
      simp only [d232, d25154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d233 q = 1) (hb : d266246 q = 1) : d25155 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d25155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d25155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234 q = 1) (hb : d266246 q = 1) : d25156 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d25156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d25156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d673 q = 1) (hb : d266246 q = 1) : d25604 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d25604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d673, d25604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d682 q = 1) (hb : d266246 q = 1) : d25613 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d682, d25613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d682, d25613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d683 q = 1) (hb : d266246 q = 1) : d25614 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d683, d25614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d683, d25614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro72872 (p : Pattern) (ha : d730 p = 1) (hb : d266246 p = 1) : d25670 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d684 q = 1) (hb : d266246 q = 1) : d25615 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d25615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72871 q ha hb
    | true =>
      simp only [d684, d25615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d685 q = 1) (hb : d266246 q = 1) : d25616 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d25616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d25616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d727 q = 1) (hb : d266246 q = 1) : d25667 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d727, d25667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d727, d25667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d728 q = 1) (hb : d266246 q = 1) : d25668 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d728, d25668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d728, d25668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d729 q = 1) (hb : d266246 q = 1) : d25669 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d729, d25669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d729, d25669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d730 q = 1) (hb : d266246 q = 1) : d25670 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d730, d25670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d730, d25670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72873 (p : Pattern) (ha : d736 p = 1) (hb : d266246 p = 1) : d25676 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d731 q = 1) (hb : d266246 q = 1) : d25671 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d731, d25671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72872 q ha hb
    | true =>
      simp only [d731, d25671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d732 q = 1) (hb : d266246 q = 1) : d25672 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d732, d25672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d732, d25672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d733 q = 1) (hb : d266246 q = 1) : d25673 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d733, d25673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d733, d25673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d734 q = 1) (hb : d266246 q = 1) : d25674 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d734, d25674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d734, d25674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d735 q = 1) (hb : d266246 q = 1) : d25675 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d735, d25675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d735, d25675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d736 q = 1) (hb : d266246 q = 1) : d25676 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d736, d25676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d736, d25676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72874 (p : Pattern) (ha : d16036 p = 1) (hb : d266246 p = 1) : d266328 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15967 q = 1) (hb : d266246 q = 1) : d266254 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d266254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72849 q ha hb
    | true =>
      simp only [d15967, d266254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72829 q ha hb
  have h2 (q : Pattern) (ha : d15968 q = 1) (hb : d266246 q = 1) : d266255 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d266255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d266255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15969 q = 1) (hb : d266246 q = 1) : d266256 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d266256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d266256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d266246 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d145 q = 1) (hb : d266246 q = 1) : d25111 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d25111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72829 q ha hb
    | true =>
      simp only [d145, d25111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146 q = 1) (hb : d266246 q = 1) : d25112 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d25112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d25112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147 q = 1) (hb : d266246 q = 1) : d25113 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d25113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d25113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15970 q = 1) (hb : d266246 q = 1) : d266257 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d266257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15970, d266257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d475 q = 1) (hb : d266246 q = 1) : d25375 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d25375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d475, d25375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16035 q = 1) (hb : d266246 q = 1) : d266327 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16035, d266327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16035, d266327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16036 q = 1) (hb : d266246 q = 1) : d266328 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16036, d266328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16036, d266328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro72875 (p : Pattern) (ha : d16042 p = 1) (hb : d266246 p = 1) : d266334 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d266246 q = 1) : d266329 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d266329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72874 q ha hb
    | true =>
      simp only [d16037, d266329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d266246 q = 1) : d266330 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d266330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d266330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d266246 q = 1) : d25382 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d25382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72866 q ha hb
    | true =>
      simp only [d482, d25382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d266246 q = 1) : d25383 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d25383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d25383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d266246 q = 1) : d266331 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d266331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d266331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d266246 q = 1) : d266332 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d266332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d266332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16041 q = 1) (hb : d266246 q = 1) : d266333 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16041, d266333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16041, d266333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16042 q = 1) (hb : d266246 q = 1) : d266334 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16042, d266334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16042, d266334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72876 (p : Pattern) (ha : d16048 p = 1) (hb : d266246 p = 1) : d266340 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16043 q = 1) (hb : d266246 q = 1) : d266335 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16043, d266335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72875 q ha hb
    | true =>
      simp only [d16043, d266335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72867 q ha hb
  have h2 (q : Pattern) (ha : d16044 q = 1) (hb : d266246 q = 1) : d266336 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16044, d266336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16044, d266336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16045 q = 1) (hb : d266246 q = 1) : d266337 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16045, d266337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16045, d266337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16046 q = 1) (hb : d266246 q = 1) : d266338 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16046, d266338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16046, d266338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16047 q = 1) (hb : d266246 q = 1) : d266339 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16047, d266339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16047, d266339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16048 q = 1) (hb : d266246 q = 1) : d266340 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16048, d266340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16048, d266340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72877 (p : Pattern) (ha : d16051 p = 1) (hb : d266246 p = 1) : d266343 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d266246 q = 1) : d266329 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d266329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72874 q ha hb
    | true =>
      simp only [d16037, d266329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d266246 q = 1) : d266330 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d266330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d266330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d266246 q = 1) : d25382 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d25382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72866 q ha hb
    | true =>
      simp only [d482, d25382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d266246 q = 1) : d25383 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d25383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d25383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d266246 q = 1) : d266331 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d266331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d266331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d266246 q = 1) : d266332 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d266332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d266332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16041 q = 1) (hb : d266246 q = 1) : d266333 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16041, d266333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16041, d266333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16051 q = 1) (hb : d266246 q = 1) : d266343 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16051, d266343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16051, d266343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro72878 (p : Pattern) (ha : d16057 p = 1) (hb : d266246 p = 1) : d266349 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16043 q = 1) (hb : d266246 q = 1) : d266335 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16043, d266335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72875 q ha hb
    | true =>
      simp only [d16043, d266335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72867 q ha hb
  have h2 (q : Pattern) (ha : d16044 q = 1) (hb : d266246 q = 1) : d266336 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16044, d266336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16044, d266336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16045 q = 1) (hb : d266246 q = 1) : d266337 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16045, d266337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16045, d266337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16046 q = 1) (hb : d266246 q = 1) : d266338 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16046, d266338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16046, d266338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16047 q = 1) (hb : d266246 q = 1) : d266339 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16047, d266339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16047, d266339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16052 q = 1) (hb : d266246 q = 1) : d266344 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16052, d266344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72877 q ha hb
    | true =>
      simp only [d16052, d266344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72868 q ha hb
  have h7 (q : Pattern) (ha : d16053 q = 1) (hb : d266246 q = 1) : d266345 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16053, d266345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16053, d266345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16054 q = 1) (hb : d266246 q = 1) : d266346 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16054, d266346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16054, d266346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16055 q = 1) (hb : d266246 q = 1) : d266347 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16055, d266347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16055, d266347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16056 q = 1) (hb : d266246 q = 1) : d266348 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16056, d266348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16056, d266348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16057 q = 1) (hb : d266246 q = 1) : d266349 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16057, d266349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16057, d266349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro72879 (p : Pattern) (ha : d16143 p = 1) (hb : d266246 p = 1) : d266426 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16043 q = 1) (hb : d266246 q = 1) : d266335 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16043, d266335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72875 q ha hb
    | true =>
      simp only [d16043, d266335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72867 q ha hb
  have h2 (q : Pattern) (ha : d16044 q = 1) (hb : d266246 q = 1) : d266336 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16044, d266336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16044, d266336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16045 q = 1) (hb : d266246 q = 1) : d266337 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16045, d266337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16045, d266337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16046 q = 1) (hb : d266246 q = 1) : d266338 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16046, d266338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16046, d266338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16047 q = 1) (hb : d266246 q = 1) : d266339 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16047, d266339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16047, d266339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d633 q = 1) (hb : d266246 q = 1) : d25551 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d25551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72867 q ha hb
    | true =>
      simp only [d633, d25551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d634 q = 1) (hb : d266246 q = 1) : d25552 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d25552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d25552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d635 q = 1) (hb : d266246 q = 1) : d25553 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d25553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d635, d25553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d636 q = 1) (hb : d266246 q = 1) : d25554 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d25554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d25554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d637 q = 1) (hb : d266246 q = 1) : d25555 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d25555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d25555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16143 q = 1) (hb : d266246 q = 1) : d266426 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16143, d266426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16143, d266426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro72880 (p : Pattern) (ha : d514 p = 1) (hb : d266246 p = 1) : d25414 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d266246 q = 1) : d25382 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d25382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72866 q ha hb
    | true =>
      simp only [d482, d25382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d266246 q = 1) : d25383 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d25383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d25383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d266246 q = 1) : d25388 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d25388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d25388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d266246 q = 1) : d25389 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d25389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d25389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d513 q = 1) (hb : d266246 q = 1) : d25413 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d25413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d25413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d514 q = 1) (hb : d266246 q = 1) : d25414 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d514, d25414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d514, d25414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72881 (p : Pattern) (ha : d524 p = 1) (hb : d266246 p = 1) : d25424 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d266246 q = 1) : d25382 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d25382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72866 q ha hb
    | true =>
      simp only [d482, d25382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d266246 q = 1) : d25383 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d25383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d25383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d266246 q = 1) : d25388 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d25388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d25388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d522 q = 1) (hb : d266246 q = 1) : d25422 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d25422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d25422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d523 q = 1) (hb : d266246 q = 1) : d25423 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d25423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d523, d25423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d524 q = 1) (hb : d266246 q = 1) : d25424 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d524, d25424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d524, d25424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72882 (p : Pattern) (ha : d16062 p = 1) (hb : d266246 p = 1) : d266354 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d266246 q = 1) : d266329 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d266329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72874 q ha hb
    | true =>
      simp only [d16037, d266329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d266246 q = 1) : d266330 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d266330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d266330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d266246 q = 1) : d25382 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d25382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72866 q ha hb
    | true =>
      simp only [d482, d25382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d266246 q = 1) : d25383 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d25383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d25383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d266246 q = 1) : d266331 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d266331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d266331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d266246 q = 1) : d266332 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d266332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d266332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16061 q = 1) (hb : d266246 q = 1) : d266353 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16061, d266353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16061, d266353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16062 q = 1) (hb : d266246 q = 1) : d266354 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16062, d266354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16062, d266354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72883 (p : Pattern) (ha : d16069 p = 1) (hb : d266246 p = 1) : d266361 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d266246 q = 1) : d266329 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d266329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72874 q ha hb
    | true =>
      simp only [d16037, d266329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d266246 q = 1) : d266330 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d266330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d266330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d266246 q = 1) : d25382 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d25382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72866 q ha hb
    | true =>
      simp only [d482, d25382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d266246 q = 1) : d25383 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d25383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d25383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d266246 q = 1) : d266331 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d266331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d266331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16067 q = 1) (hb : d266246 q = 1) : d266359 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16067, d266359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16067, d266359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16068 q = 1) (hb : d266246 q = 1) : d266360 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16068, d266360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16068, d266360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16069 q = 1) (hb : d266246 q = 1) : d266361 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16069, d266361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16069, d266361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72884 (p : Pattern) (ha : d16114 p = 1) (hb : d266246 p = 1) : d266399 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d266246 q = 1) : d266329 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d266329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72874 q ha hb
    | true =>
      simp only [d16037, d266329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d266246 q = 1) : d266330 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d266330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d266330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16111 q = 1) (hb : d266246 q = 1) : d266396 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16111, d266396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16111, d266396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16112 q = 1) (hb : d266246 q = 1) : d266397 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16112, d266397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16112, d266397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16113 q = 1) (hb : d266246 q = 1) : d266398 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16113, d266398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16113, d266398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16114 q = 1) (hb : d266246 q = 1) : d266399 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16114, d266399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16114, d266399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72885 (p : Pattern) (ha : d16081 p = 1) (hb : d266246 p = 1) : d25461 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9382 q = 1) (hb : d266246 q = 1) : d25222 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72848 q ha hb
    | true =>
      simp only [d9382, d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9384 q = 1) (hb : d266246 q = 1) : d25223 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9384, d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12493 q = 1) (hb : d266246 q = 1) : d25224 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d25224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d25224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12494 q = 1) (hb : d266246 q = 1) : d25225 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d25225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12494, d25225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d266246 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12495 q = 1) (hb : d266246 q = 1) : d25226 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12495, d25226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12495, d25226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d266246 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d16081 q = 1) (hb : d266246 q = 1) : d25461 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16081, d25461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16081, d25461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72886 (p : Pattern) (ha : d23230 p = 1) (hb : d266246 p = 1) : d25451 p = 1 := by
  have h0 (q : Pattern) (ha : d314 q = 1) (hb : d236581 q = 1) : d314 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d134 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d315 q = 1) (hb : d266244 q = 1) : d25210 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d266244, d25210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d315, d266244, d25210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d266245 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23228 q = 1) (hb : d266246 q = 1) : d25449 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23228, d266246, d25449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23228, d266246, d25449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23229 q = 1) (hb : d266246 q = 1) : d25450 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23229, d25450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23229, d25450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d134 q = 1) (hb : d236581 q = 1) : d134 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d20 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d135 q = 1) (hb : d266244 q = 1) : d9796 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d266244, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d135, d266244, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d5448 q = 1) (hb : d266246 q = 1) : d25219 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5448, d266246, d25219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5448, d266246, d25219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d5449 q = 1) (hb : d266246 q = 1) : d25220 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5449, d25220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5449, d25220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d23230 q = 1) (hb : d266246 q = 1) : d25451 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d23230, d25451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23230, d25451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro72887 (p : Pattern) (ha : d28745 p = 1) (hb : d266246 p = 1) : d266367 p = 1 := by
  have h0 (q : Pattern) (ha : d532 q = 1) (hb : d236581 q = 1) : d532 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d314 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d533 q = 1) (hb : d266244 q = 1) : d25428 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d533, d266244, d25428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d533, d266244, d25428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d28740 q = 1) (hb : d241830 q = 1) : d30971 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d28740, d241830, d30971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro71339 q ha hb
    | true =>
      simp only [d28740, d241830, d30971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d28741 q = 1) (hb : d241830 q = 1) : d30972 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d28741, d30972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28741, d30972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d134 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d28742 q = 1) (hb : d266245 q = 1) : d251674 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d28742, d266245, d251674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28742, d266245, d251674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d28743 q = 1) (hb : d266246 q = 1) : d266365 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d28743, d266246, d266365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28743, d266246, d266365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d28744 q = 1) (hb : d266246 q = 1) : d266366 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d28744, d266366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28744, d266366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d314 q = 1) (hb : d236581 q = 1) : d314 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d315 q = 1) (hb : d266244 q = 1) : d25210 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d266244, d25210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d315, d266244, d25210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h14 (q : Pattern) (ha : d133 q = 1) (hb : d241830 q = 1) : d25433 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d241830, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47928 q ha hb
    | true =>
      simp only [d133, d241830, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h15 (q : Pattern) (ha : d134 q = 1) (hb : d241830 q = 1) : d25434 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d20 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d135 q = 1) (hb : d266245 q = 1) : d25435 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d266245, d25435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d135, d266245, d25435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d316 q = 1) (hb : d266246 q = 1) : d25436 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d316, d266246, d25436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d316, d266246, d25436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d317 q = 1) (hb : d266246 q = 1) : d25437 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d317, d25437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d317, d25437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h20 (q : Pattern) (ha : d28745 q = 1) (hb : d266246 q = 1) : d266367 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d28745, d266367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d28745, d266367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro72888 (p : Pattern) (ha : d28750 p = 1) (hb : d266246 p = 1) : d266372 p = 1 := by
  have h0 (q : Pattern) (ha : d314 q = 1) (hb : d236581 q = 1) : d314 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d134 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d315 q = 1) (hb : d266244 q = 1) : d25210 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d266244, d25210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d315, d266244, d25210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d133 q = 1) (hb : d241830 q = 1) : d25433 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d241830, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47928 q ha hb
    | true =>
      simp only [d133, d241830, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d134 q = 1) (hb : d241830 q = 1) : d25434 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d20 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d135 q = 1) (hb : d266245 q = 1) : d25435 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d266245, d25435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d135, d266245, d25435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d316 q = 1) (hb : d266246 q = 1) : d25436 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d316, d266246, d25436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d316, d266246, d25436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d317 q = 1) (hb : d266246 q = 1) : d25437 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d317, d25437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d317, d25437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d134 q = 1) (hb : d236581 q = 1) : d134 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d135 q = 1) (hb : d266244 q = 1) : d9796 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d266244, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d135, d266244, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d266245 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d5448 q = 1) (hb : d266246 q = 1) : d25219 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5448, d266246, d25219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5448, d266246, d25219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d5449 q = 1) (hb : d266246 q = 1) : d25220 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5449, d25220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d5449, d25220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h17 (q : Pattern) (ha : d28750 q = 1) (hb : d266246 q = 1) : d266372 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d28750, d266372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d28750, d266372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro72889 (p : Pattern) (ha : d28756 p = 1) (hb : d266246 p = 1) : d266378 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28746 q = 1) (hb : d266246 q = 1) : d266368 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28746, d266368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72887 q ha hb
    | true =>
      simp only [d28746, d266368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28747 q = 1) (hb : d266246 q = 1) : d266369 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28747, d266369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28747, d266369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28748 q = 1) (hb : d266246 q = 1) : d266370 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28748, d266370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28748, d266370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28749 q = 1) (hb : d266246 q = 1) : d266371 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28749, d266371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28749, d266371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28751 q = 1) (hb : d266246 q = 1) : d266373 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28751, d266373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72888 q ha hb
    | true =>
      simp only [d28751, d266373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d28752 q = 1) (hb : d266246 q = 1) : d266374 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28752, d266374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28752, d266374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28753 q = 1) (hb : d266246 q = 1) : d266375 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28753, d266375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28753, d266375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28754 q = 1) (hb : d266246 q = 1) : d266376 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28754, d266376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28754, d266376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d28755 q = 1) (hb : d266246 q = 1) : d266377 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28755, d266377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28755, d266377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23231 q = 1) (hb : d266246 q = 1) : d25452 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72886 q ha hb
    | true =>
      simp only [d23231, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23232 q = 1) (hb : d266246 q = 1) : d25453 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23232, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d23233 q = 1) (hb : d266246 q = 1) : d25454 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23233, d25454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23233, d25454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23234 q = 1) (hb : d266246 q = 1) : d25455 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23234, d25455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23234, d25455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d9382 q = 1) (hb : d266246 q = 1) : d25222 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72848 q ha hb
    | true =>
      simp only [d9382, d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9384 q = 1) (hb : d266246 q = 1) : d25223 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9384, d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d12493 q = 1) (hb : d266246 q = 1) : d25224 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d25224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d25224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12494 q = 1) (hb : d266246 q = 1) : d25225 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d25225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12494, d25225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d23235 q = 1) (hb : d266246 q = 1) : d25456 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23235, d25456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23235, d25456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d28756 q = 1) (hb : d266246 q = 1) : d266378 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d28756, d266378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28756, d266378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro72890 (p : Pattern) (ha : d28762 p = 1) (hb : d266246 p = 1) : d266387 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28757 q = 1) (hb : d266246 q = 1) : d266379 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28757, d266379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72889 q ha hb
    | true =>
      simp only [d28757, d266379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72849 q ha hb
  have h2 (q : Pattern) (ha : d28758 q = 1) (hb : d266246 q = 1) : d266380 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28758, d266380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28758, d266380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28759 q = 1) (hb : d266246 q = 1) : d266381 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28759, d266381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28759, d266381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16082 q = 1) (hb : d266246 q = 1) : d266382 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16082, d266382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72849 q ha hb
    | true =>
      simp only [d16082, d266382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72885 q ha hb
  have h5 (q : Pattern) (ha : d16083 q = 1) (hb : d266246 q = 1) : d266383 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16083, d266383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16083, d266383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16084 q = 1) (hb : d266246 q = 1) : d266384 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16084, d266384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16084, d266384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28760 q = 1) (hb : d266246 q = 1) : d266385 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28760, d266385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28760, d266385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15967 q = 1) (hb : d266246 q = 1) : d266254 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d266254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72849 q ha hb
    | true =>
      simp only [d15967, d266254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72829 q ha hb
  have h9 (q : Pattern) (ha : d15968 q = 1) (hb : d266246 q = 1) : d266255 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d266255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d266255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15969 q = 1) (hb : d266246 q = 1) : d266256 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d266256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d266256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30 q = 1) (hb : d266246 q = 1) : d30 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d145 q = 1) (hb : d266246 q = 1) : d25111 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d25111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72829 q ha hb
    | true =>
      simp only [d145, d25111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d146 q = 1) (hb : d266246 q = 1) : d25112 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d25112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d25112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147 q = 1) (hb : d266246 q = 1) : d25113 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d25113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d25113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d15970 q = 1) (hb : d266246 q = 1) : d266257 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d266257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15970, d266257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d28761 q = 1) (hb : d266246 q = 1) : d266386 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d28761, d266386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28761, d266386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d28762 q = 1) (hb : d266246 q = 1) : d266387 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d28762, d266387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d28762, d266387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro72891 (p : Pattern) (ha : d28768 p = 1) (hb : d266246 p = 1) : d266393 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28763 q = 1) (hb : d266246 q = 1) : d266388 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28763, d266388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72890 q ha hb
    | true =>
      simp only [d28763, d266388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28764 q = 1) (hb : d266246 q = 1) : d266389 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28764, d266389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28764, d266389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16037 q = 1) (hb : d266246 q = 1) : d266329 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d266329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72874 q ha hb
    | true =>
      simp only [d16037, d266329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16038 q = 1) (hb : d266246 q = 1) : d266330 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d266330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d266330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28765 q = 1) (hb : d266246 q = 1) : d266390 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28765, d266390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28765, d266390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28766 q = 1) (hb : d266246 q = 1) : d266391 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28766, d266391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28766, d266391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28767 q = 1) (hb : d266246 q = 1) : d266392 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28767, d266392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28767, d266392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28768 q = 1) (hb : d266246 q = 1) : d266393 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28768, d266393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28768, d266393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72892 (p : Pattern) (ha : d238875 p = 1) (hb : d266246 p = 1) : d266405 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16063 q = 1) (hb : d266246 q = 1) : d266355 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16063, d266355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72882 q ha hb
    | true =>
      simp only [d16063, d266355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72880 q ha hb
  have h2 (q : Pattern) (ha : d16064 q = 1) (hb : d266246 q = 1) : d266356 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16064, d266356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16064, d266356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16065 q = 1) (hb : d266246 q = 1) : d266357 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16065, d266357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16065, d266357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16066 q = 1) (hb : d266246 q = 1) : d266358 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16066, d266358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16066, d266358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16070 q = 1) (hb : d266246 q = 1) : d266362 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16070, d266362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72883 q ha hb
    | true =>
      simp only [d16070, d266362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72881 q ha hb
  have h6 (q : Pattern) (ha : d16071 q = 1) (hb : d266246 q = 1) : d266363 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16071, d266363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16071, d266363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16072 q = 1) (hb : d266246 q = 1) : d266364 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16072, d266364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16072, d266364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28769 q = 1) (hb : d266246 q = 1) : d266394 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28769, d266394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72891 q ha hb
    | true =>
      simp only [d28769, d266394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72875 q ha hb
  have h9 (q : Pattern) (ha : d238871 q = 1) (hb : d266246 q = 1) : d266395 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238871, d266395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d238871, d266395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16115 q = 1) (hb : d266246 q = 1) : d266400 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16115, d266400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72884 q ha hb
    | true =>
      simp only [d16115, d266400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16116 q = 1) (hb : d266246 q = 1) : d266401 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16116, d266401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16116, d266401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d238872 q = 1) (hb : d266246 q = 1) : d266402 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238872, d266402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d238872, d266402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d238873 q = 1) (hb : d266246 q = 1) : d266403 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238873, d266403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d238873, d266403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d238874 q = 1) (hb : d266246 q = 1) : d266404 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238874, d266404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238874, d266404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d238875 q = 1) (hb : d266246 q = 1) : d266405 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238875, d266405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238875, d266405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro72893 (p : Pattern) (ha : d610 p = 1) (hb : d266246 p = 1) : d25527 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d266246 q = 1) : d25382 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d25382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72866 q ha hb
    | true =>
      simp only [d482, d25382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d266246 q = 1) : d25383 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d25383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d25383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d266246 q = 1) : d25388 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d25388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d25388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d266246 q = 1) : d25389 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d25389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d25389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d513 q = 1) (hb : d266246 q = 1) : d25413 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d25413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d25413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d610 q = 1) (hb : d266246 q = 1) : d25527 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d610, d25527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d610, d25527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72894 (p : Pattern) (ha : d616 p = 1) (hb : d266246 p = 1) : d25533 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d266246 q = 1) : d25382 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d25382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72866 q ha hb
    | true =>
      simp only [d482, d25382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d266246 q = 1) : d25383 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d25383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d25383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d266246 q = 1) : d25388 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d25388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d25388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d522 q = 1) (hb : d266246 q = 1) : d25422 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d25422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d25422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d523 q = 1) (hb : d266246 q = 1) : d25423 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d25423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d523, d25423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d616 q = 1) (hb : d266246 q = 1) : d25533 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d616, d25533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d616, d25533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72895 (p : Pattern) (ha : d16121 p = 1) (hb : d266246 p = 1) : d266406 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d266246 q = 1) : d266329 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d266329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72874 q ha hb
    | true =>
      simp only [d16037, d266329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d266246 q = 1) : d266330 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d266330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d266330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d266246 q = 1) : d25382 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d25382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72866 q ha hb
    | true =>
      simp only [d482, d25382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d266246 q = 1) : d25383 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d25383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d25383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d266246 q = 1) : d266331 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d266331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d266331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d266246 q = 1) : d266332 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d266332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d266332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16061 q = 1) (hb : d266246 q = 1) : d266353 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16061, d266353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16061, d266353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16121 q = 1) (hb : d266246 q = 1) : d266406 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16121, d266406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16121, d266406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro72896 (p : Pattern) (ha : d16126 p = 1) (hb : d266246 p = 1) : d266411 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d266246 q = 1) : d266329 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d266329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72874 q ha hb
    | true =>
      simp only [d16037, d266329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d266246 q = 1) : d266330 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d266330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d266330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d266246 q = 1) : d25382 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d25382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72866 q ha hb
    | true =>
      simp only [d482, d25382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d266246 q = 1) : d25383 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d25383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d25383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d266246 q = 1) : d266331 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d266331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d266331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16067 q = 1) (hb : d266246 q = 1) : d266359 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16067, d266359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16067, d266359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16068 q = 1) (hb : d266246 q = 1) : d266360 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16068, d266360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16068, d266360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16126 q = 1) (hb : d266246 q = 1) : d266411 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16126, d266411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16126, d266411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro72897 (p : Pattern) (ha : d16135 p = 1) (hb : d266246 p = 1) : d266418 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d266246 q = 1) : d266329 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d266329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72874 q ha hb
    | true =>
      simp only [d16037, d266329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d266246 q = 1) : d266330 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d266330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d266330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16111 q = 1) (hb : d266246 q = 1) : d266396 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16111, d266396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16111, d266396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16112 q = 1) (hb : d266246 q = 1) : d266397 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16112, d266397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16112, d266397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16113 q = 1) (hb : d266246 q = 1) : d266398 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16113, d266398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16113, d266398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16135 q = 1) (hb : d266246 q = 1) : d266418 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16135, d266418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16135, d266418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72898 (p : Pattern) (ha : d28775 p = 1) (hb : d266246 p = 1) : d266415 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28763 q = 1) (hb : d266246 q = 1) : d266388 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28763, d266388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72890 q ha hb
    | true =>
      simp only [d28763, d266388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28764 q = 1) (hb : d266246 q = 1) : d266389 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28764, d266389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28764, d266389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16037 q = 1) (hb : d266246 q = 1) : d266329 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d266329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72874 q ha hb
    | true =>
      simp only [d16037, d266329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16038 q = 1) (hb : d266246 q = 1) : d266330 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d266330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d266330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28765 q = 1) (hb : d266246 q = 1) : d266390 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28765, d266390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28765, d266390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28766 q = 1) (hb : d266246 q = 1) : d266391 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28766, d266391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28766, d266391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28767 q = 1) (hb : d266246 q = 1) : d266392 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28767, d266392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28767, d266392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28775 q = 1) (hb : d266246 q = 1) : d266415 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28775, d266415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28775, d266415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro72899 (p : Pattern) (ha : d238880 p = 1) (hb : d266246 p = 1) : d266424 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16063 q = 1) (hb : d266246 q = 1) : d266355 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16063, d266355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72882 q ha hb
    | true =>
      simp only [d16063, d266355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72880 q ha hb
  have h2 (q : Pattern) (ha : d16064 q = 1) (hb : d266246 q = 1) : d266356 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16064, d266356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16064, d266356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16065 q = 1) (hb : d266246 q = 1) : d266357 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16065, d266357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16065, d266357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16066 q = 1) (hb : d266246 q = 1) : d266358 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16066, d266358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16066, d266358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16070 q = 1) (hb : d266246 q = 1) : d266362 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16070, d266362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72883 q ha hb
    | true =>
      simp only [d16070, d266362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72881 q ha hb
  have h6 (q : Pattern) (ha : d16071 q = 1) (hb : d266246 q = 1) : d266363 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16071, d266363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16071, d266363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16072 q = 1) (hb : d266246 q = 1) : d266364 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16072, d266364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16072, d266364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28769 q = 1) (hb : d266246 q = 1) : d266394 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28769, d266394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72891 q ha hb
    | true =>
      simp only [d28769, d266394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72875 q ha hb
  have h9 (q : Pattern) (ha : d238871 q = 1) (hb : d266246 q = 1) : d266395 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238871, d266395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d238871, d266395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16115 q = 1) (hb : d266246 q = 1) : d266400 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16115, d266400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72884 q ha hb
    | true =>
      simp only [d16115, d266400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16116 q = 1) (hb : d266246 q = 1) : d266401 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16116, d266401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16116, d266401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d238872 q = 1) (hb : d266246 q = 1) : d266402 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238872, d266402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d238872, d266402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d238873 q = 1) (hb : d266246 q = 1) : d266403 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238873, d266403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d238873, d266403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d238874 q = 1) (hb : d266246 q = 1) : d266404 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238874, d266404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238874, d266404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16122 q = 1) (hb : d266246 q = 1) : d266407 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16122, d266407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72895 q ha hb
    | true =>
      simp only [d16122, d266407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72893 q ha hb
  have h16 (q : Pattern) (ha : d16123 q = 1) (hb : d266246 q = 1) : d266408 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16123, d266408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16123, d266408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16124 q = 1) (hb : d266246 q = 1) : d266409 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16124, d266409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16124, d266409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16125 q = 1) (hb : d266246 q = 1) : d266410 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16125, d266410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16125, d266410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16127 q = 1) (hb : d266246 q = 1) : d266412 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16127, d266412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72896 q ha hb
    | true =>
      simp only [d16127, d266412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72894 q ha hb
  have h20 (q : Pattern) (ha : d16128 q = 1) (hb : d266246 q = 1) : d266413 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16128, d266413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16128, d266413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d16129 q = 1) (hb : d266246 q = 1) : d266414 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16129, d266414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d16129, d266414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d28776 q = 1) (hb : d266246 q = 1) : d266416 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28776, d266416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72898 q ha hb
    | true =>
      simp only [d28776, d266416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72877 q ha hb
  have h23 (q : Pattern) (ha : d238876 q = 1) (hb : d266246 q = 1) : d266417 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238876, d266417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d238876, d266417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d16136 q = 1) (hb : d266246 q = 1) : d266419 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16136, d266419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72897 q ha hb
    | true =>
      simp only [d16136, d266419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d16137 q = 1) (hb : d266246 q = 1) : d266420 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16137, d266420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d16137, d266420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d238877 q = 1) (hb : d266246 q = 1) : d266421 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238877, d266421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d238877, d266421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d238878 q = 1) (hb : d266246 q = 1) : d266422 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238878, d266422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d238878, d266422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d238879 q = 1) (hb : d266246 q = 1) : d266423 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238879, d266423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d238879, d266423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d238880 q = 1) (hb : d266246 q = 1) : d266424 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238880, d266424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d238880, d266424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro72900 (p : Pattern) (ha : d238887 p = 1) (hb : d266246 p = 1) : d266433 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28776 q = 1) (hb : d266246 q = 1) : d266416 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28776, d266416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72898 q ha hb
    | true =>
      simp only [d28776, d266416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72877 q ha hb
  have h2 (q : Pattern) (ha : d238876 q = 1) (hb : d266246 q = 1) : d266417 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238876, d266417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238876, d266417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16136 q = 1) (hb : d266246 q = 1) : d266419 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16136, d266419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72897 q ha hb
    | true =>
      simp only [d16136, d266419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16137 q = 1) (hb : d266246 q = 1) : d266420 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16137, d266420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16137, d266420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d238877 q = 1) (hb : d266246 q = 1) : d266421 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238877, d266421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d238877, d266421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238885 q = 1) (hb : d266246 q = 1) : d266431 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238885, d266431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238885, d266431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238886 q = 1) (hb : d266246 q = 1) : d266432 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238886, d266432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238886, d266432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238887 q = 1) (hb : d266246 q = 1) : d266433 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238887, d266433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238887, d266433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72901 (p : Pattern) (ha : d16176 p = 1) (hb : d266246 p = 1) : d266461 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16005 q = 1) (hb : d266246 q = 1) : d266297 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d266297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72860 q ha hb
    | true =>
      simp only [d16005, d266297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72833 q ha hb
  have h2 (q : Pattern) (ha : d16006 q = 1) (hb : d266246 q = 1) : d266298 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d266298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d266298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16007 q = 1) (hb : d266246 q = 1) : d266299 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d266299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d266299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d266246 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d232 q = 1) (hb : d266246 q = 1) : d25154 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d25154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72833 q ha hb
    | true =>
      simp only [d232, d25154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d233 q = 1) (hb : d266246 q = 1) : d25155 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d25155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d25155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234 q = 1) (hb : d266246 q = 1) : d25156 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d25156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d25156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16008 q = 1) (hb : d266246 q = 1) : d266300 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d266300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16008, d266300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d673 q = 1) (hb : d266246 q = 1) : d25604 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d25604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d673, d25604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16175 q = 1) (hb : d266246 q = 1) : d266460 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16175, d266460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16175, d266460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16176 q = 1) (hb : d266246 q = 1) : d266461 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16176, d266461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16176, d266461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro72902 (p : Pattern) (ha : d16186 p = 1) (hb : d266246 p = 1) : d266471 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16177 q = 1) (hb : d266246 q = 1) : d266462 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16177, d266462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72901 q ha hb
    | true =>
      simp only [d16177, d266462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16178 q = 1) (hb : d266246 q = 1) : d266463 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16178, d266463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16178, d266463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d684 q = 1) (hb : d266246 q = 1) : d25615 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d25615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72871 q ha hb
    | true =>
      simp only [d684, d25615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d685 q = 1) (hb : d266246 q = 1) : d25616 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d25616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d25616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16183 q = 1) (hb : d266246 q = 1) : d266468 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16183, d266468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16183, d266468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16184 q = 1) (hb : d266246 q = 1) : d266469 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16184, d266469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16184, d266469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16185 q = 1) (hb : d266246 q = 1) : d266470 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16185, d266470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16185, d266470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16186 q = 1) (hb : d266246 q = 1) : d266471 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16186, d266471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16186, d266471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro72903 (p : Pattern) (ha : d16207 p = 1) (hb : d266246 p = 1) : d266477 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16177 q = 1) (hb : d266246 q = 1) : d266462 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16177, d266462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72901 q ha hb
    | true =>
      simp only [d16177, d266462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16178 q = 1) (hb : d266246 q = 1) : d266463 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16178, d266463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16178, d266463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16204 q = 1) (hb : d266246 q = 1) : d266474 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16204, d266474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16204, d266474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16205 q = 1) (hb : d266246 q = 1) : d266475 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16205, d266475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16205, d266475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16206 q = 1) (hb : d266246 q = 1) : d266476 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16206, d266476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16206, d266476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16207 q = 1) (hb : d266246 q = 1) : d266477 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16207, d266477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16207, d266477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72904 (p : Pattern) (ha : d16166 p = 1) (hb : d266246 p = 1) : d25595 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12599 q = 1) (hb : d266246 q = 1) : d25314 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d25314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d25314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72848 q ha hb
  have h2 (q : Pattern) (ha : d9382 q = 1) (hb : d266246 q = 1) : d25222 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72848 q ha hb
    | true =>
      simp only [d9382, d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12600 q = 1) (hb : d266246 q = 1) : d25315 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d25315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12600, d25315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9384 q = 1) (hb : d266246 q = 1) : d25223 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9384, d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12601 q = 1) (hb : d266246 q = 1) : d25316 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d25316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12601, d25316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12602 q = 1) (hb : d266246 q = 1) : d25317 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d25317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12602, d25317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d266246 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12603 q = 1) (hb : d266246 q = 1) : d25318 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12603, d25318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12603, d25318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d266246 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16166 q = 1) (hb : d266246 q = 1) : d25595 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16166, d25595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16166, d25595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro72905 (p : Pattern) (ha : d28803 p = 1) (hb : d266246 p = 1) : d266448 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28794 q = 1) (hb : d266246 q = 1) : d266439 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28794, d266439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28794, d266439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72887 q ha hb
  have h2 (q : Pattern) (ha : d28746 q = 1) (hb : d266246 q = 1) : d266368 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28746, d266368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72887 q ha hb
    | true =>
      simp only [d28746, d266368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28795 q = 1) (hb : d266246 q = 1) : d266440 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28795, d266440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28795, d266440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28747 q = 1) (hb : d266246 q = 1) : d266369 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28747, d266369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28747, d266369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28796 q = 1) (hb : d266246 q = 1) : d266441 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28796, d266441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28796, d266441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28797 q = 1) (hb : d266246 q = 1) : d266442 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28797, d266442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28797, d266442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28798 q = 1) (hb : d266246 q = 1) : d266443 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28798, d266443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28798, d266443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72888 q ha hb
  have h8 (q : Pattern) (ha : d28751 q = 1) (hb : d266246 q = 1) : d266373 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28751, d266373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72888 q ha hb
    | true =>
      simp only [d28751, d266373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d28799 q = 1) (hb : d266246 q = 1) : d266444 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28799, d266444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28799, d266444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28752 q = 1) (hb : d266246 q = 1) : d266374 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28752, d266374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d28752, d266374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d28800 q = 1) (hb : d266246 q = 1) : d266445 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28800, d266445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28800, d266445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d28801 q = 1) (hb : d266246 q = 1) : d266446 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28801, d266446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d28801, d266446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d28802 q = 1) (hb : d266246 q = 1) : d266447 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28802, d266447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28802, d266447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d23310 q = 1) (hb : d266246 q = 1) : d25586 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23310, d25586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23310, d25586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72886 q ha hb
  have h15 (q : Pattern) (ha : d23231 q = 1) (hb : d266246 q = 1) : d25452 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72886 q ha hb
    | true =>
      simp only [d23231, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d23311 q = 1) (hb : d266246 q = 1) : d25587 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23311, d25587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d23311, d25587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23232 q = 1) (hb : d266246 q = 1) : d25453 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d23232, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d23312 q = 1) (hb : d266246 q = 1) : d25588 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23312, d25588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d23312, d25588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d23313 q = 1) (hb : d266246 q = 1) : d25589 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23313, d25589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d23313, d25589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d12599 q = 1) (hb : d266246 q = 1) : d25314 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d25314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d25314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72848 q ha hb
  have h21 (q : Pattern) (ha : d9382 q = 1) (hb : d266246 q = 1) : d25222 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72848 q ha hb
    | true =>
      simp only [d9382, d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d12600 q = 1) (hb : d266246 q = 1) : d25315 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d25315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d12600, d25315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9384 q = 1) (hb : d266246 q = 1) : d25223 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d9384, d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d12601 q = 1) (hb : d266246 q = 1) : d25316 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d25316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d12601, d25316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d12602 q = 1) (hb : d266246 q = 1) : d25317 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d25317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12602, d25317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d23314 q = 1) (hb : d266246 q = 1) : d25590 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23314, d25590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d23314, d25590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d28803 q = 1) (hb : d266246 q = 1) : d266448 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d28803, d266448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d28803, d266448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro72906 (p : Pattern) (ha : d28809 p = 1) (hb : d266246 p = 1) : d266457 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28804 q = 1) (hb : d266246 q = 1) : d266449 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28804, d266449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72905 q ha hb
    | true =>
      simp only [d28804, d266449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72860 q ha hb
  have h2 (q : Pattern) (ha : d28805 q = 1) (hb : d266246 q = 1) : d266450 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28805, d266450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28805, d266450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28806 q = 1) (hb : d266246 q = 1) : d266451 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28806, d266451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28806, d266451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16167 q = 1) (hb : d266246 q = 1) : d266452 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16167, d266452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72860 q ha hb
    | true =>
      simp only [d16167, d266452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72904 q ha hb
  have h5 (q : Pattern) (ha : d16168 q = 1) (hb : d266246 q = 1) : d266453 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16168, d266453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16168, d266453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16169 q = 1) (hb : d266246 q = 1) : d266454 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16169, d266454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16169, d266454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28807 q = 1) (hb : d266246 q = 1) : d266455 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28807, d266455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28807, d266455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16005 q = 1) (hb : d266246 q = 1) : d266297 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d266297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72860 q ha hb
    | true =>
      simp only [d16005, d266297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72833 q ha hb
  have h9 (q : Pattern) (ha : d16006 q = 1) (hb : d266246 q = 1) : d266298 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d266298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d266298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16007 q = 1) (hb : d266246 q = 1) : d266299 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d266299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d266299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d71 q = 1) (hb : d266246 q = 1) : d71 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d232 q = 1) (hb : d266246 q = 1) : d25154 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d25154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72833 q ha hb
    | true =>
      simp only [d232, d25154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d233 q = 1) (hb : d266246 q = 1) : d25155 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d25155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d25155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d234 q = 1) (hb : d266246 q = 1) : d25156 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d25156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d25156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16008 q = 1) (hb : d266246 q = 1) : d266300 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d266300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16008, d266300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d28808 q = 1) (hb : d266246 q = 1) : d266456 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d28808, d266456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28808, d266456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d28809 q = 1) (hb : d266246 q = 1) : d266457 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d28809, d266457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d28809, d266457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro72907 (p : Pattern) (ha : d28815 p = 1) (hb : d266246 p = 1) : d266467 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28810 q = 1) (hb : d266246 q = 1) : d266458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28810, d266458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72906 q ha hb
    | true =>
      simp only [d28810, d266458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28811 q = 1) (hb : d266246 q = 1) : d266459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28811, d266459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28811, d266459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16177 q = 1) (hb : d266246 q = 1) : d266462 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16177, d266462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72901 q ha hb
    | true =>
      simp only [d16177, d266462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16178 q = 1) (hb : d266246 q = 1) : d266463 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16178, d266463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16178, d266463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28812 q = 1) (hb : d266246 q = 1) : d266464 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28812, d266464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28812, d266464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28813 q = 1) (hb : d266246 q = 1) : d266465 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28813, d266465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28813, d266465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28814 q = 1) (hb : d266246 q = 1) : d266466 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28814, d266466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28814, d266466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28815 q = 1) (hb : d266246 q = 1) : d266467 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28815, d266467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28815, d266467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro72908 (p : Pattern) (ha : d238897 p = 1) (hb : d266246 p = 1) : d266483 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28816 q = 1) (hb : d266246 q = 1) : d266472 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28816, d266472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72907 q ha hb
    | true =>
      simp only [d28816, d266472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72902 q ha hb
  have h2 (q : Pattern) (ha : d238893 q = 1) (hb : d266246 q = 1) : d266473 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238893, d266473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238893, d266473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16208 q = 1) (hb : d266246 q = 1) : d266478 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16208, d266478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72903 q ha hb
    | true =>
      simp only [d16208, d266478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16209 q = 1) (hb : d266246 q = 1) : d266479 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16209, d266479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16209, d266479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d238894 q = 1) (hb : d266246 q = 1) : d266480 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238894, d266480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d238894, d266480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238895 q = 1) (hb : d266246 q = 1) : d266481 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238895, d266481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238895, d266481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238896 q = 1) (hb : d266246 q = 1) : d266482 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238896, d266482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238896, d266482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238897 q = 1) (hb : d266246 q = 1) : d266483 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238897, d266483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238897, d266483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72909 (p : Pattern) (ha : d238903 p = 1) (hb : d266246 p = 1) : d266489 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16049 q = 1) (hb : d266246 q = 1) : d266341 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16049, d266341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16049, d266341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72876 q ha hb
  have h2 (q : Pattern) (ha : d16050 q = 1) (hb : d266246 q = 1) : d266342 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16050, d266342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16050, d266342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16058 q = 1) (hb : d266246 q = 1) : d266350 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16058, d266350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72876 q ha hb
    | true =>
      simp only [d16058, d266350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72878 q ha hb
  have h4 (q : Pattern) (ha : d16059 q = 1) (hb : d266246 q = 1) : d266351 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16059, d266351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16059, d266351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16060 q = 1) (hb : d266246 q = 1) : d266352 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d16060, d266352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16060, d266352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238881 q = 1) (hb : d266246 q = 1) : d266425 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238881, d266425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72892 q ha hb
    | true =>
      simp only [d238881, d266425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72899 q ha hb
  have h7 (q : Pattern) (ha : d16144 q = 1) (hb : d266246 q = 1) : d266427 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16144, d266427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72879 q ha hb
    | true =>
      simp only [d16144, d266427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72869 q ha hb
  have h8 (q : Pattern) (ha : d238882 q = 1) (hb : d266246 q = 1) : d266428 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238882, d266428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d238882, d266428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d238883 q = 1) (hb : d266246 q = 1) : d266429 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238883, d266429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d238883, d266429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d238884 q = 1) (hb : d266246 q = 1) : d266430 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238884, d266430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d238884, d266430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d238888 q = 1) (hb : d266246 q = 1) : d266434 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238888, d266434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238888, d266434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72900 q ha hb
  have h12 (q : Pattern) (ha : d654 q = 1) (hb : d266246 q = 1) : d25572 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, d25572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d654, d25572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72870 q ha hb
  have h13 (q : Pattern) (ha : d238889 q = 1) (hb : d266246 q = 1) : d266435 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238889, d266435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d238889, d266435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d238890 q = 1) (hb : d266246 q = 1) : d266436 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238890, d266436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d238890, d266436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d238891 q = 1) (hb : d266246 q = 1) : d266437 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238891, d266437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d238891, d266437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d238892 q = 1) (hb : d266246 q = 1) : d266438 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d238892, d266438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d238892, d266438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d238898 q = 1) (hb : d266246 q = 1) : d266484 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238898, d266484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238898, d266484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72908 q ha hb
  have h18 (q : Pattern) (ha : d737 q = 1) (hb : d266246 q = 1) : d25677 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, d25677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d737, d25677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72873 q ha hb
  have h19 (q : Pattern) (ha : d238899 q = 1) (hb : d266246 q = 1) : d266485 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238899, d266485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d238899, d266485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d238900 q = 1) (hb : d266246 q = 1) : d266486 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238900, d266486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d238900, d266486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d238901 q = 1) (hb : d266246 q = 1) : d266487 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238901, d266487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d238901, d266487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d238902 q = 1) (hb : d266246 q = 1) : d266488 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d238902, d266488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d238902, d266488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d238903 q = 1) (hb : d266246 q = 1) : d266489 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d238903, d266489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d238903, d266489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro72910 (p : Pattern) (ha : d238909 p = 1) (hb : d266246 p = 1) : d266495 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238904 q = 1) (hb : d266246 q = 1) : d266490 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d238904, d266490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238904, d266490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72909 q ha hb
  have h2 (q : Pattern) (ha : d238905 q = 1) (hb : d266246 q = 1) : d266491 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d238905, d266491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238905, d266491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d238906 q = 1) (hb : d266246 q = 1) : d266492 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d238906, d266492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238906, d266492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d238907 q = 1) (hb : d266246 q = 1) : d266493 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d238907, d266493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238907, d266493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d238908 q = 1) (hb : d266246 q = 1) : d266494 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d238908, d266494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238908, d266494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238909 q = 1) (hb : d266246 q = 1) : d266495 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d238909, d266495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238909, d266495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72911 (p : Pattern) (ha : d750 p = 1) (hb : d266246 p = 1) : d25690 p = 1 := by
  have h0 (q : Pattern) (ha : d134 q = 1) (hb : d236581 q = 1) : d134 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d135 q = 1) (hb : d266244 q = 1) : d9796 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d266244, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d135, d266244, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d21 q = 1) (hb : d266245 q = 1) : d21 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d136 q = 1) (hb : d266246 q = 1) : d25102 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d136, d266246, d25102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d136, d266246, d25102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d137 q = 1) (hb : d266246 q = 1) : d25103 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d137, d25103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137, d25103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d750 q = 1) (hb : d266246 q = 1) : d25690 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d750, d25690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d750, d25690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h7 p ha hb
theorem andIntro72912 (p : Pattern) (ha : d758 p = 1) (hb : d266246 p = 1) : d266499 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d266246 q = 1) : d266248 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d266248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72847 q ha hb
    | true =>
      simp only [d319, d266248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d320 q = 1) (hb : d266246 q = 1) : d266249 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d266249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320, d266249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321 q = 1) (hb : d266246 q = 1) : d266250 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d266250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d266250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d266246 q = 1) : d266251 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d266251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322, d266251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d751 q = 1) (hb : d266246 q = 1) : d25691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72911 q ha hb
    | true =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d752 q = 1) (hb : d266246 q = 1) : d25692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d753 q = 1) (hb : d266246 q = 1) : d25693 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d754 q = 1) (hb : d266246 q = 1) : d25694 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d754, d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d755 q = 1) (hb : d266246 q = 1) : d266498 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d755, d266498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d755, d266498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d757 q = 1) (hb : d266246 q = 1) : d25698 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d25698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d757, d25698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d758 q = 1) (hb : d266246 q = 1) : d266499 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d758, d266499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d758, d266499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro72913 (p : Pattern) (ha : d762 p = 1) (hb : d266246 p = 1) : d25703 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d751 q = 1) (hb : d266246 q = 1) : d25691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72911 q ha hb
    | true =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d752 q = 1) (hb : d266246 q = 1) : d25692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d753 q = 1) (hb : d266246 q = 1) : d25693 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d754 q = 1) (hb : d266246 q = 1) : d25694 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d754, d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d757 q = 1) (hb : d266246 q = 1) : d25698 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d25698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d757, d25698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d762 q = 1) (hb : d266246 q = 1) : d25703 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d762, d25703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d762, d25703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72914 (p : Pattern) (ha : d773 p = 1) (hb : d266246 p = 1) : d266513 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d763 q = 1) (hb : d266246 q = 1) : d266503 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d266503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72912 q ha hb
    | true =>
      simp only [d763, d266503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72913 q ha hb
  have h2 (q : Pattern) (ha : d764 q = 1) (hb : d266246 q = 1) : d266504 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d266504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d266504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d765 q = 1) (hb : d266246 q = 1) : d266505 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d266505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d266505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d767 q = 1) (hb : d266246 q = 1) : d266507 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d266507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d767, d266507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d772 q = 1) (hb : d266246 q = 1) : d266512 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d772, d266512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d772, d266512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d773 q = 1) (hb : d266246 q = 1) : d266513 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d773, d266513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d773, d266513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72915 (p : Pattern) (ha : d783 p = 1) (hb : d266246 p = 1) : d266523 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d266246 q = 1) : d266514 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d266514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72914 q ha hb
    | true =>
      simp only [d774, d266514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d266246 q = 1) : d266515 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d266515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d266515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d266246 q = 1) : d266520 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d266520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d266520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d266246 q = 1) : d266521 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d266521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d266521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d266246 q = 1) : d266522 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d266522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, d266522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d783 q = 1) (hb : d266246 q = 1) : d266523 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d783, d266523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d783, d266523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72916 (p : Pattern) (ha : d793 p = 1) (hb : d266246 p = 1) : d266533 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d266246 q = 1) : d266514 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d266514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72914 q ha hb
    | true =>
      simp only [d774, d266514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d266246 q = 1) : d266515 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d266515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d266515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d266246 q = 1) : d266520 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d266520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d266520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d266246 q = 1) : d266521 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d266521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d266521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d266246 q = 1) : d266522 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d266522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, d266522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d793 q = 1) (hb : d266246 q = 1) : d266533 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d793, d266533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d793, d266533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72917 (p : Pattern) (ha : d950 p = 1) (hb : d266246 p = 1) : d266634 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d939 q = 1) (hb : d266246 q = 1) : d266623 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d266623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72915 q ha hb
    | true =>
      simp only [d939, d266623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d940 q = 1) (hb : d266246 q = 1) : d266624 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d266624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d266624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d941 q = 1) (hb : d266246 q = 1) : d266625 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d266625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d941, d266625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d942 q = 1) (hb : d266246 q = 1) : d266626 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d266626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d266626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d943 q = 1) (hb : d266246 q = 1) : d266627 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d266627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d266627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d945 q = 1) (hb : d266246 q = 1) : d266629 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d266629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72916 q ha hb
    | true =>
      simp only [d945, d266629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d946 q = 1) (hb : d266246 q = 1) : d266630 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d266630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, d266630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d947 q = 1) (hb : d266246 q = 1) : d266631 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d266631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d947, d266631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d948 q = 1) (hb : d266246 q = 1) : d266632 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d266632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, d266632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d949 q = 1) (hb : d266246 q = 1) : d266633 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d266633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, d266633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d950 q = 1) (hb : d266246 q = 1) : d266634 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d950, d266634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d950, d266634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro72918 (p : Pattern) (ha : d959 p = 1) (hb : d266246 p = 1) : d266643 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d945 q = 1) (hb : d266246 q = 1) : d266629 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d266629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72916 q ha hb
    | true =>
      simp only [d945, d266629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d946 q = 1) (hb : d266246 q = 1) : d266630 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d266630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, d266630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d947 q = 1) (hb : d266246 q = 1) : d266631 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d266631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d947, d266631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d948 q = 1) (hb : d266246 q = 1) : d266632 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d266632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, d266632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d949 q = 1) (hb : d266246 q = 1) : d266633 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d266633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, d266633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d959 q = 1) (hb : d266246 q = 1) : d266643 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d959, d266643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d959, d266643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72919 (p : Pattern) (ha : d981 p = 1) (hb : d266246 p = 1) : d266668 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d412 q = 1) (hb : d266246 q = 1) : d266291 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d266291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d266291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72847 q ha hb
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d266246 q = 1) : d266248 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d266248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72847 q ha hb
    | true =>
      simp only [d319, d266248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d413 q = 1) (hb : d266246 q = 1) : d266292 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d266292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d413, d266292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320 q = 1) (hb : d266246 q = 1) : d266249 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d266249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d266249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d414 q = 1) (hb : d266246 q = 1) : d266293 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d266293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d414, d266293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d415 q = 1) (hb : d266246 q = 1) : d266294 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d266294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d415, d266294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d971 q = 1) (hb : d266246 q = 1) : d25948 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72911 q ha hb
  have h8 (q : Pattern) (ha : d751 q = 1) (hb : d266246 q = 1) : d25691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72911 q ha hb
    | true =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d972 q = 1) (hb : d266246 q = 1) : d25949 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d972, d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d752 q = 1) (hb : d266246 q = 1) : d25692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d973 q = 1) (hb : d266246 q = 1) : d25950 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d973, d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d974 q = 1) (hb : d266246 q = 1) : d25951 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d974, d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d975 q = 1) (hb : d266246 q = 1) : d266667 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d975, d266667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d975, d266667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d980 q = 1) (hb : d266246 q = 1) : d25957 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d25957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d980, d25957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d981 q = 1) (hb : d266246 q = 1) : d266668 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d981, d266668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d981, d266668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro72920 (p : Pattern) (ha : d986 p = 1) (hb : d266246 p = 1) : d25968 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d971 q = 1) (hb : d266246 q = 1) : d25948 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72911 q ha hb
  have h2 (q : Pattern) (ha : d751 q = 1) (hb : d266246 q = 1) : d25691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72911 q ha hb
    | true =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d972 q = 1) (hb : d266246 q = 1) : d25949 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d972, d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d752 q = 1) (hb : d266246 q = 1) : d25692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d973 q = 1) (hb : d266246 q = 1) : d25950 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d973, d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d974 q = 1) (hb : d266246 q = 1) : d25951 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d974, d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d980 q = 1) (hb : d266246 q = 1) : d25957 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d25957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d980, d25957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d986 q = 1) (hb : d266246 q = 1) : d25968 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d986, d25968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d986, d25968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro72921 (p : Pattern) (ha : d1005 p = 1) (hb : d266246 p = 1) : d266690 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d987 q = 1) (hb : d266246 q = 1) : d266672 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d266672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72919 q ha hb
    | true =>
      simp only [d987, d266672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72920 q ha hb
  have h2 (q : Pattern) (ha : d988 q = 1) (hb : d266246 q = 1) : d266673 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d266673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d266673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d989 q = 1) (hb : d266246 q = 1) : d266674 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d266674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d266674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d995 q = 1) (hb : d266246 q = 1) : d266680 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d266680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d995, d266680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1004 q = 1) (hb : d266246 q = 1) : d266689 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1004, d266689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1004, d266689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1005 q = 1) (hb : d266246 q = 1) : d266690 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1005, d266690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1005, d266690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72922 (p : Pattern) (ha : d1063 p = 1) (hb : d266246 p = 1) : d266713 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1006 q = 1) (hb : d266246 q = 1) : d266691 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d266691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72921 q ha hb
    | true =>
      simp only [d1006, d266691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1007 q = 1) (hb : d266246 q = 1) : d266692 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d266692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d266692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1060 q = 1) (hb : d266246 q = 1) : d266710 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1060, d266710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1060, d266710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1061 q = 1) (hb : d266246 q = 1) : d266711 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1061, d266711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1061, d266711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1062 q = 1) (hb : d266246 q = 1) : d266712 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1062, d266712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1062, d266712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1063 q = 1) (hb : d266246 q = 1) : d266713 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1063, d266713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1063, d266713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72923 (p : Pattern) (ha : d1069 p = 1) (hb : d266246 p = 1) : d266719 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1064 q = 1) (hb : d266246 q = 1) : d266714 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1064, d266714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72922 q ha hb
    | true =>
      simp only [d1064, d266714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1065 q = 1) (hb : d266246 q = 1) : d266715 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1065, d266715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1065, d266715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1066 q = 1) (hb : d266246 q = 1) : d266716 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1066, d266716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1066, d266716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1067 q = 1) (hb : d266246 q = 1) : d266717 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1067, d266717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1067, d266717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1068 q = 1) (hb : d266246 q = 1) : d266718 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1068, d266718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1068, d266718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1069 q = 1) (hb : d266246 q = 1) : d266719 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1069, d266719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1069, d266719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72924 (p : Pattern) (ha : d28836 p = 1) (hb : d266246 p = 1) : d266497 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28746 q = 1) (hb : d266246 q = 1) : d266368 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28746, d266368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72887 q ha hb
    | true =>
      simp only [d28746, d266368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28747 q = 1) (hb : d266246 q = 1) : d266369 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28747, d266369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28747, d266369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28748 q = 1) (hb : d266246 q = 1) : d266370 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28748, d266370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28748, d266370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28749 q = 1) (hb : d266246 q = 1) : d266371 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28749, d266371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28749, d266371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28751 q = 1) (hb : d266246 q = 1) : d266373 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28751, d266373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72888 q ha hb
    | true =>
      simp only [d28751, d266373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d28752 q = 1) (hb : d266246 q = 1) : d266374 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28752, d266374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28752, d266374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28753 q = 1) (hb : d266246 q = 1) : d266375 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28753, d266375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28753, d266375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28754 q = 1) (hb : d266246 q = 1) : d266376 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28754, d266376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28754, d266376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d28755 q = 1) (hb : d266246 q = 1) : d266377 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28755, d266377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28755, d266377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23231 q = 1) (hb : d266246 q = 1) : d25452 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72886 q ha hb
    | true =>
      simp only [d23231, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23232 q = 1) (hb : d266246 q = 1) : d25453 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23232, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d23233 q = 1) (hb : d266246 q = 1) : d25454 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23233, d25454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23233, d25454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23234 q = 1) (hb : d266246 q = 1) : d25455 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23234, d25455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23234, d25455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d751 q = 1) (hb : d266246 q = 1) : d25691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72911 q ha hb
    | true =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d752 q = 1) (hb : d266246 q = 1) : d25692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d753 q = 1) (hb : d266246 q = 1) : d25693 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d754 q = 1) (hb : d266246 q = 1) : d25694 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d754, d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d28835 q = 1) (hb : d266246 q = 1) : d25695 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28835, d25695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d28835, d25695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d28836 q = 1) (hb : d266246 q = 1) : d266497 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d28836, d266497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28836, d266497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro72925 (p : Pattern) (ha : d28842 p = 1) (hb : d266246 p = 1) : d266509 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28837 q = 1) (hb : d266246 q = 1) : d266500 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28837, d266500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72924 q ha hb
    | true =>
      simp only [d28837, d266500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72912 q ha hb
  have h2 (q : Pattern) (ha : d28838 q = 1) (hb : d266246 q = 1) : d266501 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28838, d266501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28838, d266501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28839 q = 1) (hb : d266246 q = 1) : d266502 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28839, d266502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28839, d266502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d763 q = 1) (hb : d266246 q = 1) : d266503 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d266503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72912 q ha hb
    | true =>
      simp only [d763, d266503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72913 q ha hb
  have h5 (q : Pattern) (ha : d764 q = 1) (hb : d266246 q = 1) : d266504 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d266504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d266504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d765 q = 1) (hb : d266246 q = 1) : d266505 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d266505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d266505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28840 q = 1) (hb : d266246 q = 1) : d266506 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28840, d266506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28840, d266506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d767 q = 1) (hb : d266246 q = 1) : d266507 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d266507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d767, d266507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d28841 q = 1) (hb : d266246 q = 1) : d266508 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d28841, d266508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28841, d266508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28842 q = 1) (hb : d266246 q = 1) : d266509 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d28842, d266509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28842, d266509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro72926 (p : Pattern) (ha : d28848 p = 1) (hb : d266246 p = 1) : d266519 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28843 q = 1) (hb : d266246 q = 1) : d266510 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28843, d266510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72925 q ha hb
    | true =>
      simp only [d28843, d266510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28844 q = 1) (hb : d266246 q = 1) : d266511 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28844, d266511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28844, d266511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d266246 q = 1) : d266514 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d266514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72914 q ha hb
    | true =>
      simp only [d774, d266514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d266246 q = 1) : d266515 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d266515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d266515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28845 q = 1) (hb : d266246 q = 1) : d266516 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28845, d266516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28845, d266516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28846 q = 1) (hb : d266246 q = 1) : d266517 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28846, d266517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28846, d266517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28847 q = 1) (hb : d266246 q = 1) : d266518 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28847, d266518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28847, d266518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28848 q = 1) (hb : d266246 q = 1) : d266519 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28848, d266519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28848, d266519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72927 (p : Pattern) (ha : d28854 p = 1) (hb : d266246 p = 1) : d266529 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28849 q = 1) (hb : d266246 q = 1) : d266524 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28849, d266524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72926 q ha hb
    | true =>
      simp only [d28849, d266524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72915 q ha hb
  have h2 (q : Pattern) (ha : d28850 q = 1) (hb : d266246 q = 1) : d266525 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28850, d266525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28850, d266525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28851 q = 1) (hb : d266246 q = 1) : d266526 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28851, d266526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28851, d266526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28852 q = 1) (hb : d266246 q = 1) : d266527 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28852, d266527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28852, d266527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28853 q = 1) (hb : d266246 q = 1) : d266528 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d28853, d266528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28853, d266528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28854 q = 1) (hb : d266246 q = 1) : d266529 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d28854, d266529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28854, d266529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72928 (p : Pattern) (ha : d28857 p = 1) (hb : d266246 p = 1) : d266532 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28843 q = 1) (hb : d266246 q = 1) : d266510 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28843, d266510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72925 q ha hb
    | true =>
      simp only [d28843, d266510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28844 q = 1) (hb : d266246 q = 1) : d266511 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28844, d266511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28844, d266511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d266246 q = 1) : d266514 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d266514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72914 q ha hb
    | true =>
      simp only [d774, d266514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d266246 q = 1) : d266515 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d266515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d266515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28845 q = 1) (hb : d266246 q = 1) : d266516 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28845, d266516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28845, d266516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28846 q = 1) (hb : d266246 q = 1) : d266517 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28846, d266517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28846, d266517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28847 q = 1) (hb : d266246 q = 1) : d266518 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28847, d266518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28847, d266518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28857 q = 1) (hb : d266246 q = 1) : d266532 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28857, d266532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28857, d266532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro72929 (p : Pattern) (ha : d28863 p = 1) (hb : d266246 p = 1) : d266539 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28849 q = 1) (hb : d266246 q = 1) : d266524 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28849, d266524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72926 q ha hb
    | true =>
      simp only [d28849, d266524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72915 q ha hb
  have h2 (q : Pattern) (ha : d28850 q = 1) (hb : d266246 q = 1) : d266525 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28850, d266525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28850, d266525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28851 q = 1) (hb : d266246 q = 1) : d266526 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28851, d266526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28851, d266526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28852 q = 1) (hb : d266246 q = 1) : d266527 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28852, d266527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28852, d266527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28853 q = 1) (hb : d266246 q = 1) : d266528 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d28853, d266528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28853, d266528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28858 q = 1) (hb : d266246 q = 1) : d266534 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28858, d266534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72928 q ha hb
    | true =>
      simp only [d28858, d266534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72916 q ha hb
  have h7 (q : Pattern) (ha : d28859 q = 1) (hb : d266246 q = 1) : d266535 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28859, d266535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28859, d266535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28860 q = 1) (hb : d266246 q = 1) : d266536 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28860, d266536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28860, d266536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d28861 q = 1) (hb : d266246 q = 1) : d266537 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28861, d266537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28861, d266537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28862 q = 1) (hb : d266246 q = 1) : d266538 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d28862, d266538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28862, d266538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d28863 q = 1) (hb : d266246 q = 1) : d266539 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d28863, d266539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28863, d266539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro72930 (p : Pattern) (ha : d28985 p = 1) (hb : d266246 p = 1) : d266628 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28849 q = 1) (hb : d266246 q = 1) : d266524 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28849, d266524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72926 q ha hb
    | true =>
      simp only [d28849, d266524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72915 q ha hb
  have h2 (q : Pattern) (ha : d28850 q = 1) (hb : d266246 q = 1) : d266525 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28850, d266525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28850, d266525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28851 q = 1) (hb : d266246 q = 1) : d266526 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28851, d266526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28851, d266526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28852 q = 1) (hb : d266246 q = 1) : d266527 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28852, d266527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28852, d266527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28853 q = 1) (hb : d266246 q = 1) : d266528 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d28853, d266528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28853, d266528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d939 q = 1) (hb : d266246 q = 1) : d266623 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d266623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72915 q ha hb
    | true =>
      simp only [d939, d266623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d940 q = 1) (hb : d266246 q = 1) : d266624 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d266624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d266624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d941 q = 1) (hb : d266246 q = 1) : d266625 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d266625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d941, d266625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d942 q = 1) (hb : d266246 q = 1) : d266626 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d266626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d266626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d943 q = 1) (hb : d266246 q = 1) : d266627 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d266627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d266627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d28985 q = 1) (hb : d266246 q = 1) : d266628 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d28985, d266628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28985, d266628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro72931 (p : Pattern) (ha : d806 p = 1) (hb : d266246 p = 1) : d266546 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d266246 q = 1) : d266514 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d266514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72914 q ha hb
    | true =>
      simp only [d774, d266514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d266246 q = 1) : d266515 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d266515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d266515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d266246 q = 1) : d266520 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d266520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d266520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d266246 q = 1) : d266521 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d266521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d266521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d266246 q = 1) : d266545 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d266545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d266545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d806 q = 1) (hb : d266246 q = 1) : d266546 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d806, d266546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d806, d266546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72932 (p : Pattern) (ha : d816 p = 1) (hb : d266246 p = 1) : d266556 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d266246 q = 1) : d266514 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d266514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72914 q ha hb
    | true =>
      simp only [d774, d266514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d266246 q = 1) : d266515 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d266515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d266515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d266246 q = 1) : d266520 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d266520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d266520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d266246 q = 1) : d266554 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d266554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d266554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d266246 q = 1) : d266555 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d266555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, d266555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d816 q = 1) (hb : d266246 q = 1) : d266556 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d816, d266556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d816, d266556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72933 (p : Pattern) (ha : d28868 p = 1) (hb : d266246 p = 1) : d266544 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28843 q = 1) (hb : d266246 q = 1) : d266510 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28843, d266510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72925 q ha hb
    | true =>
      simp only [d28843, d266510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28844 q = 1) (hb : d266246 q = 1) : d266511 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28844, d266511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28844, d266511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d266246 q = 1) : d266514 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d266514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72914 q ha hb
    | true =>
      simp only [d774, d266514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d266246 q = 1) : d266515 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d266515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d266515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28845 q = 1) (hb : d266246 q = 1) : d266516 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28845, d266516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28845, d266516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28846 q = 1) (hb : d266246 q = 1) : d266517 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28846, d266517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28846, d266517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28867 q = 1) (hb : d266246 q = 1) : d266543 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28867, d266543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28867, d266543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28868 q = 1) (hb : d266246 q = 1) : d266544 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28868, d266544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28868, d266544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72934 (p : Pattern) (ha : d28875 p = 1) (hb : d266246 p = 1) : d266553 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28843 q = 1) (hb : d266246 q = 1) : d266510 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28843, d266510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72925 q ha hb
    | true =>
      simp only [d28843, d266510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28844 q = 1) (hb : d266246 q = 1) : d266511 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28844, d266511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28844, d266511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d266246 q = 1) : d266514 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d266514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72914 q ha hb
    | true =>
      simp only [d774, d266514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d266246 q = 1) : d266515 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d266515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d266515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28845 q = 1) (hb : d266246 q = 1) : d266516 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28845, d266516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28845, d266516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28873 q = 1) (hb : d266246 q = 1) : d266551 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28873, d266551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28873, d266551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28874 q = 1) (hb : d266246 q = 1) : d266552 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28874, d266552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28874, d266552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28875 q = 1) (hb : d266246 q = 1) : d266553 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28875, d266553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28875, d266553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72935 (p : Pattern) (ha : d23421 p = 1) (hb : d266246 p = 1) : d25783 p = 1 := by
  have h0 (q : Pattern) (ha : d532 q = 1) (hb : d236581 q = 1) : d532 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d314 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d533 q = 1) (hb : d266244 q = 1) : d25428 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d533, d266244, d25428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d533, d266244, d25428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d266245 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23419 q = 1) (hb : d266246 q = 1) : d25781 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23419, d266246, d25781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23419, d266246, d25781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23420 q = 1) (hb : d266246 q = 1) : d25782 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23420, d25782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23420, d25782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d314 q = 1) (hb : d236581 q = 1) : d314 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d134 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d315 q = 1) (hb : d266244 q = 1) : d25210 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d266244, d25210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d315, d266244, d25210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d23228 q = 1) (hb : d266246 q = 1) : d25449 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23228, d266246, d25449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23228, d266246, d25449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d23229 q = 1) (hb : d266246 q = 1) : d25450 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23229, d25450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23229, d25450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d23421 q = 1) (hb : d266246 q = 1) : d25783 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d23421, d25783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23421, d25783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro72936 (p : Pattern) (ha : d28891 p = 1) (hb : d266246 p = 1) : d266562 p = 1 := by
  have h0 (q : Pattern) (ha : d823 q = 1) (hb : d236581 q = 1) : d823 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d532 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d824 q = 1) (hb : d266244 q = 1) : d9759 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d824, d266244, d9759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d824, d266244, d9759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d28881 q = 1) (hb : d241830 q = 1) : d28881 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d28884 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d28885 q = 1) (hb : d266245 q = 1) : d251925 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d28885, d266245, d251925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28885, d266245, d251925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d28886 q = 1) (hb : d266246 q = 1) : d266560 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d28886, d266246, d266560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28886, d266246, d266560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d28887 q = 1) (hb : d266246 q = 1) : d266561 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d28887, d266561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28887, d266561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d532 q = 1) (hb : d236581 q = 1) : d532 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d314 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d533 q = 1) (hb : d266244 q = 1) : d25428 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d533, d266244, d25428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d533, d266244, d25428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d28883 q = 1) (hb : d241830 q = 1) : d25765 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d28883, d241830, d25765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro71389 q ha hb
    | true =>
      simp only [d28883, d241830, d25765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d28884 q = 1) (hb : d241830 q = 1) : d25766 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d28884, d25766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d28884, d25766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d134 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d28888 q = 1) (hb : d266245 q = 1) : d25767 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d28888, d266245, d25767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d28888, d266245, d25767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d28889 q = 1) (hb : d266246 q = 1) : d25768 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d28889, d266246, d25768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d28889, d266246, d25768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d28890 q = 1) (hb : d266246 q = 1) : d25769 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d28890, d25769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d28890, d25769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h20 (q : Pattern) (ha : d28891 q = 1) (hb : d266246 q = 1) : d266562 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d28891, d266562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d28891, d266562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro72937 (p : Pattern) (ha : d28896 p = 1) (hb : d266246 p = 1) : d266567 p = 1 := by
  have h0 (q : Pattern) (ha : d532 q = 1) (hb : d236581 q = 1) : d532 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d314 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d533 q = 1) (hb : d266244 q = 1) : d25428 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d533, d266244, d25428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d533, d266244, d25428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d28740 q = 1) (hb : d241830 q = 1) : d30971 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d28740, d241830, d30971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro71339 q ha hb
    | true =>
      simp only [d28740, d241830, d30971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d28741 q = 1) (hb : d241830 q = 1) : d30972 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d28741, d30972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28741, d30972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d134 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d28742 q = 1) (hb : d266245 q = 1) : d251674 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d28742, d266245, d251674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28742, d266245, d251674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d28743 q = 1) (hb : d266246 q = 1) : d266365 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d28743, d266246, d266365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28743, d266246, d266365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d28744 q = 1) (hb : d266246 q = 1) : d266366 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d28744, d266366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28744, d266366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d314 q = 1) (hb : d236581 q = 1) : d314 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d315 q = 1) (hb : d266244 q = 1) : d25210 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d266244, d25210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d315, d266244, d25210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d266245 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d23228 q = 1) (hb : d266246 q = 1) : d25449 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23228, d266246, d25449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23228, d266246, d25449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d23229 q = 1) (hb : d266246 q = 1) : d25450 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23229, d25450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d23229, d25450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h17 (q : Pattern) (ha : d28896 q = 1) (hb : d266246 q = 1) : d266567 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d28896, d266567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d28896, d266567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro72938 (p : Pattern) (ha : d28902 p = 1) (hb : d266246 p = 1) : d266573 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28892 q = 1) (hb : d266246 q = 1) : d266563 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28892, d266563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72936 q ha hb
    | true =>
      simp only [d28892, d266563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28893 q = 1) (hb : d266246 q = 1) : d266564 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28893, d266564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28893, d266564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28894 q = 1) (hb : d266246 q = 1) : d266565 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28894, d266565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28894, d266565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28895 q = 1) (hb : d266246 q = 1) : d266566 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28895, d266566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28895, d266566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28897 q = 1) (hb : d266246 q = 1) : d266568 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28897, d266568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72937 q ha hb
    | true =>
      simp only [d28897, d266568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d28898 q = 1) (hb : d266246 q = 1) : d266569 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28898, d266569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28898, d266569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28899 q = 1) (hb : d266246 q = 1) : d266570 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28899, d266570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28899, d266570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28900 q = 1) (hb : d266246 q = 1) : d266571 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28900, d266571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28900, d266571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d28901 q = 1) (hb : d266246 q = 1) : d266572 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28901, d266572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28901, d266572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23422 q = 1) (hb : d266246 q = 1) : d25784 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d25784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72935 q ha hb
    | true =>
      simp only [d23422, d25784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23423 q = 1) (hb : d266246 q = 1) : d25785 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d25785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23423, d25785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d23424 q = 1) (hb : d266246 q = 1) : d25786 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23424, d25786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23424, d25786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23425 q = 1) (hb : d266246 q = 1) : d25787 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23425, d25787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23425, d25787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d23231 q = 1) (hb : d266246 q = 1) : d25452 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72886 q ha hb
    | true =>
      simp only [d23231, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d23232 q = 1) (hb : d266246 q = 1) : d25453 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d23232, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d23233 q = 1) (hb : d266246 q = 1) : d25454 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23233, d25454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23233, d25454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23234 q = 1) (hb : d266246 q = 1) : d25455 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23234, d25455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d23234, d25455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d23426 q = 1) (hb : d266246 q = 1) : d25788 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23426, d25788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23426, d25788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d28902 q = 1) (hb : d266246 q = 1) : d266573 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d28902, d266573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28902, d266573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro72939 (p : Pattern) (ha : d28906 p = 1) (hb : d266246 p = 1) : d25793 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23231 q = 1) (hb : d266246 q = 1) : d25452 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72886 q ha hb
    | true =>
      simp only [d23231, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23232 q = 1) (hb : d266246 q = 1) : d25453 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23232, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23233 q = 1) (hb : d266246 q = 1) : d25454 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23233, d25454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23233, d25454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23234 q = 1) (hb : d266246 q = 1) : d25455 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23234, d25455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23234, d25455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d751 q = 1) (hb : d266246 q = 1) : d25691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72911 q ha hb
    | true =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d752 q = 1) (hb : d266246 q = 1) : d25692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d753 q = 1) (hb : d266246 q = 1) : d25693 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d754 q = 1) (hb : d266246 q = 1) : d25694 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d754, d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d28835 q = 1) (hb : d266246 q = 1) : d25695 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28835, d25695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28835, d25695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d757 q = 1) (hb : d266246 q = 1) : d25698 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d25698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d757, d25698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d28906 q = 1) (hb : d266246 q = 1) : d25793 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d28906, d25793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28906, d25793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro72940 (p : Pattern) (ha : d28912 p = 1) (hb : d266246 p = 1) : d266582 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28903 q = 1) (hb : d266246 q = 1) : d266574 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28903, d266574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72938 q ha hb
    | true =>
      simp only [d28903, d266574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72924 q ha hb
  have h2 (q : Pattern) (ha : d28904 q = 1) (hb : d266246 q = 1) : d266575 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28904, d266575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28904, d266575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28905 q = 1) (hb : d266246 q = 1) : d266576 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28905, d266576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28905, d266576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28907 q = 1) (hb : d266246 q = 1) : d266577 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28907, d266577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72924 q ha hb
    | true =>
      simp only [d28907, d266577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72939 q ha hb
  have h5 (q : Pattern) (ha : d28908 q = 1) (hb : d266246 q = 1) : d266578 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28908, d266578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28908, d266578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28909 q = 1) (hb : d266246 q = 1) : d266579 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28909, d266579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28909, d266579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28910 q = 1) (hb : d266246 q = 1) : d266580 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28910, d266580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28910, d266580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28837 q = 1) (hb : d266246 q = 1) : d266500 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28837, d266500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72924 q ha hb
    | true =>
      simp only [d28837, d266500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72912 q ha hb
  have h9 (q : Pattern) (ha : d28838 q = 1) (hb : d266246 q = 1) : d266501 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28838, d266501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28838, d266501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28839 q = 1) (hb : d266246 q = 1) : d266502 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28839, d266502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28839, d266502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d763 q = 1) (hb : d266246 q = 1) : d266503 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d266503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72912 q ha hb
    | true =>
      simp only [d763, d266503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72913 q ha hb
  have h12 (q : Pattern) (ha : d764 q = 1) (hb : d266246 q = 1) : d266504 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d266504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d266504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d765 q = 1) (hb : d266246 q = 1) : d266505 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d266505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d266505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d28840 q = 1) (hb : d266246 q = 1) : d266506 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28840, d266506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d28840, d266506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d28911 q = 1) (hb : d266246 q = 1) : d266581 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d28911, d266581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28911, d266581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d28912 q = 1) (hb : d266246 q = 1) : d266582 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d28912, d266582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d28912, d266582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro72941 (p : Pattern) (ha : d28918 p = 1) (hb : d266246 p = 1) : d266588 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28913 q = 1) (hb : d266246 q = 1) : d266583 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28913, d266583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72940 q ha hb
    | true =>
      simp only [d28913, d266583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28914 q = 1) (hb : d266246 q = 1) : d266584 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28914, d266584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28914, d266584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28843 q = 1) (hb : d266246 q = 1) : d266510 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28843, d266510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72925 q ha hb
    | true =>
      simp only [d28843, d266510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28844 q = 1) (hb : d266246 q = 1) : d266511 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28844, d266511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28844, d266511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28915 q = 1) (hb : d266246 q = 1) : d266585 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28915, d266585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28915, d266585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28916 q = 1) (hb : d266246 q = 1) : d266586 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28916, d266586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28916, d266586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28917 q = 1) (hb : d266246 q = 1) : d266587 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28917, d266587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28917, d266587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28918 q = 1) (hb : d266246 q = 1) : d266588 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28918, d266588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28918, d266588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72942 (p : Pattern) (ha : d28956 p = 1) (hb : d266246 p = 1) : d266594 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28843 q = 1) (hb : d266246 q = 1) : d266510 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28843, d266510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72925 q ha hb
    | true =>
      simp only [d28843, d266510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28844 q = 1) (hb : d266246 q = 1) : d266511 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28844, d266511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28844, d266511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28953 q = 1) (hb : d266246 q = 1) : d266591 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28953, d266591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28953, d266591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28954 q = 1) (hb : d266246 q = 1) : d266592 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28954, d266592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28954, d266592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28955 q = 1) (hb : d266246 q = 1) : d266593 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28955, d266593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28955, d266593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d28956 q = 1) (hb : d266246 q = 1) : d266594 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28956, d266594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28956, d266594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72943 (p : Pattern) (ha : d238915 p = 1) (hb : d266246 p = 1) : d266600 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28869 q = 1) (hb : d266246 q = 1) : d266547 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28869, d266547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72933 q ha hb
    | true =>
      simp only [d28869, d266547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72931 q ha hb
  have h2 (q : Pattern) (ha : d28870 q = 1) (hb : d266246 q = 1) : d266548 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28870, d266548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28870, d266548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28871 q = 1) (hb : d266246 q = 1) : d266549 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28871, d266549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28871, d266549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28872 q = 1) (hb : d266246 q = 1) : d266550 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28872, d266550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28872, d266550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28876 q = 1) (hb : d266246 q = 1) : d266557 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28876, d266557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72934 q ha hb
    | true =>
      simp only [d28876, d266557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72932 q ha hb
  have h6 (q : Pattern) (ha : d28877 q = 1) (hb : d266246 q = 1) : d266558 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28877, d266558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28877, d266558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28878 q = 1) (hb : d266246 q = 1) : d266559 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28878, d266559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28878, d266559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28919 q = 1) (hb : d266246 q = 1) : d266589 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28919, d266589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72941 q ha hb
    | true =>
      simp only [d28919, d266589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72926 q ha hb
  have h9 (q : Pattern) (ha : d238911 q = 1) (hb : d266246 q = 1) : d266590 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238911, d266590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d238911, d266590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d28957 q = 1) (hb : d266246 q = 1) : d266595 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28957, d266595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72942 q ha hb
    | true =>
      simp only [d28957, d266595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d28958 q = 1) (hb : d266246 q = 1) : d266596 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28958, d266596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d28958, d266596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d238912 q = 1) (hb : d266246 q = 1) : d266597 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238912, d266597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d238912, d266597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d238913 q = 1) (hb : d266246 q = 1) : d266598 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238913, d266598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d238913, d266598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d238914 q = 1) (hb : d266246 q = 1) : d266599 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238914, d266599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238914, d266599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d238915 q = 1) (hb : d266246 q = 1) : d266600 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238915, d266600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238915, d266600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro72944 (p : Pattern) (ha : d916 p = 1) (hb : d266246 p = 1) : d266602 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d266246 q = 1) : d266514 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d266514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72914 q ha hb
    | true =>
      simp only [d774, d266514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d266246 q = 1) : d266515 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d266515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d266515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d266246 q = 1) : d266520 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d266520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d266520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d266246 q = 1) : d266521 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d266521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d266521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d266246 q = 1) : d266545 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d266545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d266545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d916 q = 1) (hb : d266246 q = 1) : d266602 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d916, d266602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d916, d266602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72945 (p : Pattern) (ha : d922 p = 1) (hb : d266246 p = 1) : d266608 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d266246 q = 1) : d266514 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d266514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72914 q ha hb
    | true =>
      simp only [d774, d266514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d266246 q = 1) : d266515 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d266515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d266515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d266246 q = 1) : d266520 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d266520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d266520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d266246 q = 1) : d266554 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d266554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d266554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d266246 q = 1) : d266555 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d266555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, d266555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d922 q = 1) (hb : d266246 q = 1) : d266608 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d922, d266608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d922, d266608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72946 (p : Pattern) (ha : d28963 p = 1) (hb : d266246 p = 1) : d266601 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28843 q = 1) (hb : d266246 q = 1) : d266510 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28843, d266510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72925 q ha hb
    | true =>
      simp only [d28843, d266510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28844 q = 1) (hb : d266246 q = 1) : d266511 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28844, d266511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28844, d266511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d266246 q = 1) : d266514 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d266514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72914 q ha hb
    | true =>
      simp only [d774, d266514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d266246 q = 1) : d266515 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d266515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d266515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28845 q = 1) (hb : d266246 q = 1) : d266516 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28845, d266516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28845, d266516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28846 q = 1) (hb : d266246 q = 1) : d266517 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28846, d266517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28846, d266517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28867 q = 1) (hb : d266246 q = 1) : d266543 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28867, d266543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28867, d266543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28963 q = 1) (hb : d266246 q = 1) : d266601 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28963, d266601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28963, d266601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro72947 (p : Pattern) (ha : d28968 p = 1) (hb : d266246 p = 1) : d266607 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28843 q = 1) (hb : d266246 q = 1) : d266510 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28843, d266510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72925 q ha hb
    | true =>
      simp only [d28843, d266510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28844 q = 1) (hb : d266246 q = 1) : d266511 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28844, d266511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28844, d266511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d266246 q = 1) : d266514 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d266514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72914 q ha hb
    | true =>
      simp only [d774, d266514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d266246 q = 1) : d266515 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d266515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d266515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28845 q = 1) (hb : d266246 q = 1) : d266516 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28845, d266516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28845, d266516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28873 q = 1) (hb : d266246 q = 1) : d266551 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28873, d266551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28873, d266551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28874 q = 1) (hb : d266246 q = 1) : d266552 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28874, d266552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28874, d266552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28968 q = 1) (hb : d266246 q = 1) : d266607 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28968, d266607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28968, d266607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro72948 (p : Pattern) (ha : d28972 p = 1) (hb : d266246 p = 1) : d266612 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28913 q = 1) (hb : d266246 q = 1) : d266583 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28913, d266583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72940 q ha hb
    | true =>
      simp only [d28913, d266583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28914 q = 1) (hb : d266246 q = 1) : d266584 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28914, d266584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28914, d266584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28843 q = 1) (hb : d266246 q = 1) : d266510 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28843, d266510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72925 q ha hb
    | true =>
      simp only [d28843, d266510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28844 q = 1) (hb : d266246 q = 1) : d266511 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28844, d266511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28844, d266511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28915 q = 1) (hb : d266246 q = 1) : d266585 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28915, d266585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28915, d266585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28916 q = 1) (hb : d266246 q = 1) : d266586 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28916, d266586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28916, d266586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28917 q = 1) (hb : d266246 q = 1) : d266587 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28917, d266587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28917, d266587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28972 q = 1) (hb : d266246 q = 1) : d266612 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28972, d266612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28972, d266612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro72949 (p : Pattern) (ha : d28977 p = 1) (hb : d266246 p = 1) : d266615 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28843 q = 1) (hb : d266246 q = 1) : d266510 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28843, d266510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72925 q ha hb
    | true =>
      simp only [d28843, d266510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28844 q = 1) (hb : d266246 q = 1) : d266511 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28844, d266511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28844, d266511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28953 q = 1) (hb : d266246 q = 1) : d266591 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28953, d266591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28953, d266591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28954 q = 1) (hb : d266246 q = 1) : d266592 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28954, d266592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28954, d266592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28955 q = 1) (hb : d266246 q = 1) : d266593 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28955, d266593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28955, d266593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d28977 q = 1) (hb : d266246 q = 1) : d266615 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28977, d266615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28977, d266615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72950 (p : Pattern) (ha : d238920 p = 1) (hb : d266246 p = 1) : d266621 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28869 q = 1) (hb : d266246 q = 1) : d266547 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28869, d266547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72933 q ha hb
    | true =>
      simp only [d28869, d266547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72931 q ha hb
  have h2 (q : Pattern) (ha : d28870 q = 1) (hb : d266246 q = 1) : d266548 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28870, d266548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28870, d266548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28871 q = 1) (hb : d266246 q = 1) : d266549 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28871, d266549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28871, d266549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28872 q = 1) (hb : d266246 q = 1) : d266550 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28872, d266550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28872, d266550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28876 q = 1) (hb : d266246 q = 1) : d266557 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28876, d266557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72934 q ha hb
    | true =>
      simp only [d28876, d266557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72932 q ha hb
  have h6 (q : Pattern) (ha : d28877 q = 1) (hb : d266246 q = 1) : d266558 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28877, d266558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28877, d266558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28878 q = 1) (hb : d266246 q = 1) : d266559 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28878, d266559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28878, d266559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28919 q = 1) (hb : d266246 q = 1) : d266589 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28919, d266589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72941 q ha hb
    | true =>
      simp only [d28919, d266589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72926 q ha hb
  have h9 (q : Pattern) (ha : d238911 q = 1) (hb : d266246 q = 1) : d266590 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238911, d266590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d238911, d266590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d28957 q = 1) (hb : d266246 q = 1) : d266595 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28957, d266595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72942 q ha hb
    | true =>
      simp only [d28957, d266595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d28958 q = 1) (hb : d266246 q = 1) : d266596 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28958, d266596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d28958, d266596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d238912 q = 1) (hb : d266246 q = 1) : d266597 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238912, d266597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d238912, d266597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d238913 q = 1) (hb : d266246 q = 1) : d266598 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238913, d266598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d238913, d266598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d238914 q = 1) (hb : d266246 q = 1) : d266599 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238914, d266599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238914, d266599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d28964 q = 1) (hb : d266246 q = 1) : d266603 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28964, d266603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72946 q ha hb
    | true =>
      simp only [d28964, d266603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72944 q ha hb
  have h16 (q : Pattern) (ha : d28965 q = 1) (hb : d266246 q = 1) : d266604 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28965, d266604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28965, d266604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d28966 q = 1) (hb : d266246 q = 1) : d266605 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28966, d266605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d28966, d266605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d28967 q = 1) (hb : d266246 q = 1) : d266606 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28967, d266606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28967, d266606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d28969 q = 1) (hb : d266246 q = 1) : d266609 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28969, d266609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72947 q ha hb
    | true =>
      simp only [d28969, d266609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72945 q ha hb
  have h20 (q : Pattern) (ha : d28970 q = 1) (hb : d266246 q = 1) : d266610 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28970, d266610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28970, d266610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d28971 q = 1) (hb : d266246 q = 1) : d266611 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28971, d266611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d28971, d266611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d28973 q = 1) (hb : d266246 q = 1) : d266613 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28973, d266613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72948 q ha hb
    | true =>
      simp only [d28973, d266613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72928 q ha hb
  have h23 (q : Pattern) (ha : d238916 q = 1) (hb : d266246 q = 1) : d266614 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238916, d266614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d238916, d266614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d28978 q = 1) (hb : d266246 q = 1) : d266616 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28978, d266616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72949 q ha hb
    | true =>
      simp only [d28978, d266616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d28979 q = 1) (hb : d266246 q = 1) : d266617 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28979, d266617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d28979, d266617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d238917 q = 1) (hb : d266246 q = 1) : d266618 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238917, d266618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d238917, d266618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d238918 q = 1) (hb : d266246 q = 1) : d266619 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238918, d266619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d238918, d266619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d238919 q = 1) (hb : d266246 q = 1) : d266620 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238919, d266620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d238919, d266620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d238920 q = 1) (hb : d266246 q = 1) : d266621 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238920, d266621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d238920, d266621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro72951 (p : Pattern) (ha : d238927 p = 1) (hb : d266246 p = 1) : d266641 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28973 q = 1) (hb : d266246 q = 1) : d266613 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28973, d266613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72948 q ha hb
    | true =>
      simp only [d28973, d266613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72928 q ha hb
  have h2 (q : Pattern) (ha : d238916 q = 1) (hb : d266246 q = 1) : d266614 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238916, d266614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238916, d266614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28978 q = 1) (hb : d266246 q = 1) : d266616 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28978, d266616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72949 q ha hb
    | true =>
      simp only [d28978, d266616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28979 q = 1) (hb : d266246 q = 1) : d266617 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28979, d266617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28979, d266617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d238917 q = 1) (hb : d266246 q = 1) : d266618 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238917, d266618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d238917, d266618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238925 q = 1) (hb : d266246 q = 1) : d266639 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238925, d266639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238925, d266639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238926 q = 1) (hb : d266246 q = 1) : d266640 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238926, d266640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238926, d266640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238927 q = 1) (hb : d266246 q = 1) : d266641 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238927, d266641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238927, d266641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72952 (p : Pattern) (ha : d29007 p = 1) (hb : d266246 p = 1) : d266658 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28998 q = 1) (hb : d266246 q = 1) : d266649 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28998, d266649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28998, d266649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72936 q ha hb
  have h2 (q : Pattern) (ha : d28892 q = 1) (hb : d266246 q = 1) : d266563 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28892, d266563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72936 q ha hb
    | true =>
      simp only [d28892, d266563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28999 q = 1) (hb : d266246 q = 1) : d266650 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28999, d266650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28999, d266650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28893 q = 1) (hb : d266246 q = 1) : d266564 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28893, d266564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28893, d266564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29000 q = 1) (hb : d266246 q = 1) : d266651 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29000, d266651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29000, d266651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29001 q = 1) (hb : d266246 q = 1) : d266652 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29001, d266652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29001, d266652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29002 q = 1) (hb : d266246 q = 1) : d266653 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29002, d266653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29002, d266653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72937 q ha hb
  have h8 (q : Pattern) (ha : d28897 q = 1) (hb : d266246 q = 1) : d266568 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28897, d266568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72937 q ha hb
    | true =>
      simp only [d28897, d266568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d29003 q = 1) (hb : d266246 q = 1) : d266654 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29003, d266654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29003, d266654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28898 q = 1) (hb : d266246 q = 1) : d266569 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28898, d266569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d28898, d266569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d29004 q = 1) (hb : d266246 q = 1) : d266655 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29004, d266655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29004, d266655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d29005 q = 1) (hb : d266246 q = 1) : d266656 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29005, d266656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d29005, d266656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d29006 q = 1) (hb : d266246 q = 1) : d266657 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29006, d266657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29006, d266657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d23534 q = 1) (hb : d266246 q = 1) : d25942 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23534, d25942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23534, d25942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72935 q ha hb
  have h15 (q : Pattern) (ha : d23422 q = 1) (hb : d266246 q = 1) : d25784 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d25784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72935 q ha hb
    | true =>
      simp only [d23422, d25784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d23535 q = 1) (hb : d266246 q = 1) : d25943 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23535, d25943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d23535, d25943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23423 q = 1) (hb : d266246 q = 1) : d25785 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d25785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d23423, d25785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d23536 q = 1) (hb : d266246 q = 1) : d25944 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23536, d25944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d23536, d25944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d23537 q = 1) (hb : d266246 q = 1) : d25945 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23537, d25945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d23537, d25945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d23310 q = 1) (hb : d266246 q = 1) : d25586 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23310, d25586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23310, d25586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72886 q ha hb
  have h21 (q : Pattern) (ha : d23231 q = 1) (hb : d266246 q = 1) : d25452 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72886 q ha hb
    | true =>
      simp only [d23231, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d23311 q = 1) (hb : d266246 q = 1) : d25587 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23311, d25587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d23311, d25587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d23232 q = 1) (hb : d266246 q = 1) : d25453 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d23232, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d23312 q = 1) (hb : d266246 q = 1) : d25588 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23312, d25588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d23312, d25588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d23313 q = 1) (hb : d266246 q = 1) : d25589 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23313, d25589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d23313, d25589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d23538 q = 1) (hb : d266246 q = 1) : d25946 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23538, d25946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d23538, d25946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d29007 q = 1) (hb : d266246 q = 1) : d266658 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d29007, d266658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d29007, d266658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro72953 (p : Pattern) (ha : d29009 p = 1) (hb : d266246 p = 1) : d266659 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28794 q = 1) (hb : d266246 q = 1) : d266439 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28794, d266439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28794, d266439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72887 q ha hb
  have h2 (q : Pattern) (ha : d28746 q = 1) (hb : d266246 q = 1) : d266368 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28746, d266368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72887 q ha hb
    | true =>
      simp only [d28746, d266368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28795 q = 1) (hb : d266246 q = 1) : d266440 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28795, d266440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28795, d266440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28747 q = 1) (hb : d266246 q = 1) : d266369 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28747, d266369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28747, d266369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28796 q = 1) (hb : d266246 q = 1) : d266441 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28796, d266441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28796, d266441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28797 q = 1) (hb : d266246 q = 1) : d266442 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28797, d266442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28797, d266442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28798 q = 1) (hb : d266246 q = 1) : d266443 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28798, d266443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28798, d266443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72888 q ha hb
  have h8 (q : Pattern) (ha : d28751 q = 1) (hb : d266246 q = 1) : d266373 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28751, d266373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72888 q ha hb
    | true =>
      simp only [d28751, d266373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d28799 q = 1) (hb : d266246 q = 1) : d266444 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28799, d266444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28799, d266444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28752 q = 1) (hb : d266246 q = 1) : d266374 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28752, d266374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d28752, d266374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d28800 q = 1) (hb : d266246 q = 1) : d266445 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28800, d266445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28800, d266445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d28801 q = 1) (hb : d266246 q = 1) : d266446 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28801, d266446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d28801, d266446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d28802 q = 1) (hb : d266246 q = 1) : d266447 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28802, d266447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28802, d266447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d23310 q = 1) (hb : d266246 q = 1) : d25586 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23310, d25586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23310, d25586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72886 q ha hb
  have h15 (q : Pattern) (ha : d23231 q = 1) (hb : d266246 q = 1) : d25452 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72886 q ha hb
    | true =>
      simp only [d23231, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d23311 q = 1) (hb : d266246 q = 1) : d25587 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23311, d25587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d23311, d25587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23232 q = 1) (hb : d266246 q = 1) : d25453 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d23232, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d23312 q = 1) (hb : d266246 q = 1) : d25588 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23312, d25588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d23312, d25588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d23313 q = 1) (hb : d266246 q = 1) : d25589 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23313, d25589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d23313, d25589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d971 q = 1) (hb : d266246 q = 1) : d25948 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72911 q ha hb
  have h21 (q : Pattern) (ha : d751 q = 1) (hb : d266246 q = 1) : d25691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72911 q ha hb
    | true =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d972 q = 1) (hb : d266246 q = 1) : d25949 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d972, d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d752 q = 1) (hb : d266246 q = 1) : d25692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d973 q = 1) (hb : d266246 q = 1) : d25950 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d973, d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d974 q = 1) (hb : d266246 q = 1) : d25951 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d974, d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d29008 q = 1) (hb : d266246 q = 1) : d25952 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29008, d25952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d29008, d25952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d29009 q = 1) (hb : d266246 q = 1) : d266659 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d29009, d266659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d29009, d266659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro72954 (p : Pattern) (ha : d29013 p = 1) (hb : d266246 p = 1) : d25958 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23310 q = 1) (hb : d266246 q = 1) : d25586 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23310, d25586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23310, d25586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72886 q ha hb
  have h2 (q : Pattern) (ha : d23231 q = 1) (hb : d266246 q = 1) : d25452 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72886 q ha hb
    | true =>
      simp only [d23231, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23311 q = 1) (hb : d266246 q = 1) : d25587 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23311, d25587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23311, d25587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23232 q = 1) (hb : d266246 q = 1) : d25453 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23232, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23312 q = 1) (hb : d266246 q = 1) : d25588 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23312, d25588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23312, d25588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23313 q = 1) (hb : d266246 q = 1) : d25589 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23313, d25589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23313, d25589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d971 q = 1) (hb : d266246 q = 1) : d25948 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72911 q ha hb
  have h8 (q : Pattern) (ha : d751 q = 1) (hb : d266246 q = 1) : d25691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72911 q ha hb
    | true =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d972 q = 1) (hb : d266246 q = 1) : d25949 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d972, d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d752 q = 1) (hb : d266246 q = 1) : d25692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d973 q = 1) (hb : d266246 q = 1) : d25950 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d973, d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d974 q = 1) (hb : d266246 q = 1) : d25951 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d974, d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d29008 q = 1) (hb : d266246 q = 1) : d25952 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29008, d25952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29008, d25952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d980 q = 1) (hb : d266246 q = 1) : d25957 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d25957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d980, d25957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d29013 q = 1) (hb : d266246 q = 1) : d25958 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d29013, d25958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d29013, d25958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro72955 (p : Pattern) (ha : d29023 p = 1) (hb : d266246 p = 1) : d266677 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29010 q = 1) (hb : d266246 q = 1) : d266660 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29010, d266660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72952 q ha hb
    | true =>
      simp only [d29010, d266660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72953 q ha hb
  have h2 (q : Pattern) (ha : d29011 q = 1) (hb : d266246 q = 1) : d266661 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29011, d266661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29011, d266661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29012 q = 1) (hb : d266246 q = 1) : d266662 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29012, d266662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29012, d266662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d29014 q = 1) (hb : d266246 q = 1) : d266663 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29014, d266663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72953 q ha hb
    | true =>
      simp only [d29014, d266663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72954 q ha hb
  have h5 (q : Pattern) (ha : d29015 q = 1) (hb : d266246 q = 1) : d266664 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29015, d266664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29015, d266664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29016 q = 1) (hb : d266246 q = 1) : d266665 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29016, d266665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29016, d266665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29017 q = 1) (hb : d266246 q = 1) : d266666 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d29017, d266666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29017, d266666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d29018 q = 1) (hb : d266246 q = 1) : d266669 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29018, d266669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72953 q ha hb
    | true =>
      simp only [d29018, d266669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72919 q ha hb
  have h9 (q : Pattern) (ha : d29019 q = 1) (hb : d266246 q = 1) : d266670 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29019, d266670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29019, d266670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29020 q = 1) (hb : d266246 q = 1) : d266671 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29020, d266671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29020, d266671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d987 q = 1) (hb : d266246 q = 1) : d266672 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d266672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72919 q ha hb
    | true =>
      simp only [d987, d266672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72920 q ha hb
  have h12 (q : Pattern) (ha : d988 q = 1) (hb : d266246 q = 1) : d266673 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d266673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d266673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d989 q = 1) (hb : d266246 q = 1) : d266674 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d266674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d266674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d29021 q = 1) (hb : d266246 q = 1) : d266675 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d29021, d266675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d29021, d266675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d29022 q = 1) (hb : d266246 q = 1) : d266676 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d29022, d266676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29022, d266676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d29023 q = 1) (hb : d266246 q = 1) : d266677 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d29023, d266677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d29023, d266677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro72956 (p : Pattern) (ha : d29027 p = 1) (hb : d266246 p = 1) : d266682 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29018 q = 1) (hb : d266246 q = 1) : d266669 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29018, d266669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72953 q ha hb
    | true =>
      simp only [d29018, d266669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72919 q ha hb
  have h2 (q : Pattern) (ha : d29019 q = 1) (hb : d266246 q = 1) : d266670 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29019, d266670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29019, d266670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29020 q = 1) (hb : d266246 q = 1) : d266671 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29020, d266671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29020, d266671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d987 q = 1) (hb : d266246 q = 1) : d266672 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d266672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72919 q ha hb
    | true =>
      simp only [d987, d266672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72920 q ha hb
  have h5 (q : Pattern) (ha : d988 q = 1) (hb : d266246 q = 1) : d266673 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d266673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d266673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d989 q = 1) (hb : d266246 q = 1) : d266674 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d266674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d266674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29021 q = 1) (hb : d266246 q = 1) : d266675 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d29021, d266675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29021, d266675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d995 q = 1) (hb : d266246 q = 1) : d266680 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d266680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d995, d266680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d29026 q = 1) (hb : d266246 q = 1) : d266681 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d29026, d266681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29026, d266681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29027 q = 1) (hb : d266246 q = 1) : d266682 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d29027, d266682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29027, d266682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro72957 (p : Pattern) (ha : d29033 p = 1) (hb : d266246 p = 1) : d266688 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29024 q = 1) (hb : d266246 q = 1) : d266678 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29024, d266678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72955 q ha hb
    | true =>
      simp only [d29024, d266678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29025 q = 1) (hb : d266246 q = 1) : d266679 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29025, d266679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29025, d266679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29028 q = 1) (hb : d266246 q = 1) : d266683 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29028, d266683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72956 q ha hb
    | true =>
      simp only [d29028, d266683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29029 q = 1) (hb : d266246 q = 1) : d266684 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29029, d266684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29029, d266684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29030 q = 1) (hb : d266246 q = 1) : d266685 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29030, d266685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29030, d266685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29031 q = 1) (hb : d266246 q = 1) : d266686 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29031, d266686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29031, d266686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29032 q = 1) (hb : d266246 q = 1) : d266687 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29032, d266687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29032, d266687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d29033 q = 1) (hb : d266246 q = 1) : d266688 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29033, d266688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29033, d266688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro72958 (p : Pattern) (ha : d29037 p = 1) (hb : d266246 p = 1) : d266696 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29028 q = 1) (hb : d266246 q = 1) : d266683 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29028, d266683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72956 q ha hb
    | true =>
      simp only [d29028, d266683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29029 q = 1) (hb : d266246 q = 1) : d266684 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29029, d266684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29029, d266684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1006 q = 1) (hb : d266246 q = 1) : d266691 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d266691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72921 q ha hb
    | true =>
      simp only [d1006, d266691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1007 q = 1) (hb : d266246 q = 1) : d266692 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d266692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d266692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29034 q = 1) (hb : d266246 q = 1) : d266693 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29034, d266693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29034, d266693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29035 q = 1) (hb : d266246 q = 1) : d266694 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29035, d266694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29035, d266694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29036 q = 1) (hb : d266246 q = 1) : d266695 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29036, d266695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29036, d266695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d29037 q = 1) (hb : d266246 q = 1) : d266696 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29037, d266696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29037, d266696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro72959 (p : Pattern) (ha : d29067 p = 1) (hb : d266246 p = 1) : d266702 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29028 q = 1) (hb : d266246 q = 1) : d266683 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29028, d266683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72956 q ha hb
    | true =>
      simp only [d29028, d266683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29029 q = 1) (hb : d266246 q = 1) : d266684 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29029, d266684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29029, d266684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29064 q = 1) (hb : d266246 q = 1) : d266699 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29064, d266699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29064, d266699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29065 q = 1) (hb : d266246 q = 1) : d266700 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29065, d266700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29065, d266700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29066 q = 1) (hb : d266246 q = 1) : d266701 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29066, d266701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29066, d266701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d29067 q = 1) (hb : d266246 q = 1) : d266702 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29067, d266702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29067, d266702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72960 (p : Pattern) (ha : d238937 p = 1) (hb : d266246 p = 1) : d266708 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29038 q = 1) (hb : d266246 q = 1) : d266697 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d29038, d266697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72957 q ha hb
    | true =>
      simp only [d29038, d266697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72958 q ha hb
  have h2 (q : Pattern) (ha : d238933 q = 1) (hb : d266246 q = 1) : d266698 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238933, d266698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238933, d266698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d29068 q = 1) (hb : d266246 q = 1) : d266703 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d29068, d266703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72959 q ha hb
    | true =>
      simp only [d29068, d266703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29069 q = 1) (hb : d266246 q = 1) : d266704 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d29069, d266704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29069, d266704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d238934 q = 1) (hb : d266246 q = 1) : d266705 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238934, d266705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d238934, d266705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238935 q = 1) (hb : d266246 q = 1) : d266706 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238935, d266706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238935, d266706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238936 q = 1) (hb : d266246 q = 1) : d266707 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238936, d266707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238936, d266707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238937 q = 1) (hb : d266246 q = 1) : d266708 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238937, d266708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238937, d266708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72961 (p : Pattern) (ha : d238943 p = 1) (hb : d266246 p = 1) : d266725 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28855 q = 1) (hb : d266246 q = 1) : d266530 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d28855, d266530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28855, d266530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72927 q ha hb
  have h2 (q : Pattern) (ha : d28856 q = 1) (hb : d266246 q = 1) : d266531 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d28856, d266531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28856, d266531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28864 q = 1) (hb : d266246 q = 1) : d266540 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d28864, d266540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72927 q ha hb
    | true =>
      simp only [d28864, d266540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72929 q ha hb
  have h4 (q : Pattern) (ha : d28865 q = 1) (hb : d266246 q = 1) : d266541 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d28865, d266541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28865, d266541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28866 q = 1) (hb : d266246 q = 1) : d266542 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d28866, d266542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28866, d266542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238921 q = 1) (hb : d266246 q = 1) : d266622 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238921, d266622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72943 q ha hb
    | true =>
      simp only [d238921, d266622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72950 q ha hb
  have h7 (q : Pattern) (ha : d28986 q = 1) (hb : d266246 q = 1) : d266635 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d28986, d266635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72930 q ha hb
    | true =>
      simp only [d28986, d266635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72917 q ha hb
  have h8 (q : Pattern) (ha : d238922 q = 1) (hb : d266246 q = 1) : d266636 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238922, d266636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d238922, d266636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d238923 q = 1) (hb : d266246 q = 1) : d266637 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238923, d266637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d238923, d266637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d238924 q = 1) (hb : d266246 q = 1) : d266638 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238924, d266638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d238924, d266638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d238928 q = 1) (hb : d266246 q = 1) : d266642 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238928, d266642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238928, d266642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72951 q ha hb
  have h12 (q : Pattern) (ha : d960 q = 1) (hb : d266246 q = 1) : d266644 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, d266644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d960, d266644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72918 q ha hb
  have h13 (q : Pattern) (ha : d238929 q = 1) (hb : d266246 q = 1) : d266645 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238929, d266645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d238929, d266645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d238930 q = 1) (hb : d266246 q = 1) : d266646 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238930, d266646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d238930, d266646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d238931 q = 1) (hb : d266246 q = 1) : d266647 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238931, d266647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d238931, d266647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d238932 q = 1) (hb : d266246 q = 1) : d266648 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d238932, d266648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d238932, d266648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d238938 q = 1) (hb : d266246 q = 1) : d266709 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238938, d266709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238938, d266709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72960 q ha hb
  have h18 (q : Pattern) (ha : d1070 q = 1) (hb : d266246 q = 1) : d266720 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, d266720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1070, d266720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72923 q ha hb
  have h19 (q : Pattern) (ha : d238939 q = 1) (hb : d266246 q = 1) : d266721 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238939, d266721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d238939, d266721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d238940 q = 1) (hb : d266246 q = 1) : d266722 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238940, d266722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d238940, d266722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d238941 q = 1) (hb : d266246 q = 1) : d266723 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238941, d266723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d238941, d266723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d238942 q = 1) (hb : d266246 q = 1) : d266724 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d238942, d266724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d238942, d266724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d238943 q = 1) (hb : d266246 q = 1) : d266725 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d238943, d266725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d238943, d266725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro72962 (p : Pattern) (ha : d238949 p = 1) (hb : d266246 p = 1) : d266731 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238944 q = 1) (hb : d266246 q = 1) : d266726 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d238944, d266726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238944, d266726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72961 q ha hb
  have h2 (q : Pattern) (ha : d238945 q = 1) (hb : d266246 q = 1) : d266727 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d238945, d266727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238945, d266727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d238946 q = 1) (hb : d266246 q = 1) : d266728 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d238946, d266728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238946, d266728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d238947 q = 1) (hb : d266246 q = 1) : d266729 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d238947, d266729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238947, d266729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d238948 q = 1) (hb : d266246 q = 1) : d266730 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d238948, d266730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238948, d266730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238949 q = 1) (hb : d266246 q = 1) : d266731 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d238949, d266731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238949, d266731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72963 (p : Pattern) (ha : d29093 p = 1) (hb : d266246 p = 1) : d266734 p = 1 := by
  have h0 (q : Pattern) (ha : d314 q = 1) (hb : d236581 q = 1) : d314 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d134 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d315 q = 1) (hb : d266244 q = 1) : d25210 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d266244, d25210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d315, d266244, d25210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d133 q = 1) (hb : d241830 q = 1) : d25433 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d241830, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47928 q ha hb
    | true =>
      simp only [d133, d241830, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d134 q = 1) (hb : d241830 q = 1) : d25434 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9796 q = 1) (hb : d266245 q = 1) : d25435 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9796, d266245, d25435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9796, d266245, d25435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d29088 q = 1) (hb : d266246 q = 1) : d25436 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d29088, d266246, d25436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29088, d266246, d25436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d29089 q = 1) (hb : d266246 q = 1) : d25437 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d29089, d25437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29089, d25437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d20 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d29090 q = 1) (hb : d266244 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d29090, d266244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d29090, d266244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d21 q = 1) (hb : d266245 q = 1) : d21 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d29091 q = 1) (hb : d266246 q = 1) : d29112 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d29091, d266246, d29112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d29091, d266246, d29112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d29092 q = 1) (hb : d266246 q = 1) : d29113 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d29092, d29113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d29092, d29113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h17 (q : Pattern) (ha : d29093 q = 1) (hb : d266246 q = 1) : d266734 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d29093, d266734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d29093, d266734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro72964 (p : Pattern) (ha : d29099 p = 1) (hb : d266246 p = 1) : d266740 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28892 q = 1) (hb : d266246 q = 1) : d266563 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28892, d266563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72936 q ha hb
    | true =>
      simp only [d28892, d266563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28893 q = 1) (hb : d266246 q = 1) : d266564 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28893, d266564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28893, d266564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28894 q = 1) (hb : d266246 q = 1) : d266565 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28894, d266565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28894, d266565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28895 q = 1) (hb : d266246 q = 1) : d266566 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28895, d266566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28895, d266566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28897 q = 1) (hb : d266246 q = 1) : d266568 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28897, d266568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72937 q ha hb
    | true =>
      simp only [d28897, d266568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d28898 q = 1) (hb : d266246 q = 1) : d266569 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28898, d266569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28898, d266569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28899 q = 1) (hb : d266246 q = 1) : d266570 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28899, d266570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28899, d266570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28900 q = 1) (hb : d266246 q = 1) : d266571 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28900, d266571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28900, d266571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d28901 q = 1) (hb : d266246 q = 1) : d266572 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28901, d266572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28901, d266572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23422 q = 1) (hb : d266246 q = 1) : d25784 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d25784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72935 q ha hb
    | true =>
      simp only [d23422, d25784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23423 q = 1) (hb : d266246 q = 1) : d25785 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d25785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23423, d25785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d23424 q = 1) (hb : d266246 q = 1) : d25786 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23424, d25786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23424, d25786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23425 q = 1) (hb : d266246 q = 1) : d25787 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23425, d25787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23425, d25787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d29094 q = 1) (hb : d266246 q = 1) : d266735 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29094, d266735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72963 q ha hb
    | true =>
      simp only [d29094, d266735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d29095 q = 1) (hb : d266246 q = 1) : d266736 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29095, d266736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d29095, d266736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d29096 q = 1) (hb : d266246 q = 1) : d266737 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29096, d266737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29096, d266737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d29097 q = 1) (hb : d266246 q = 1) : d266738 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29097, d266738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d29097, d266738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d29098 q = 1) (hb : d266246 q = 1) : d266739 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29098, d266739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d29098, d266739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d29099 q = 1) (hb : d266246 q = 1) : d266740 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d29099, d266740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29099, d266740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro72965 (p : Pattern) (ha : d29100 p = 1) (hb : d266246 p = 1) : d266734 p = 1 := by
  have h0 (q : Pattern) (ha : d314 q = 1) (hb : d236581 q = 1) : d314 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d134 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d315 q = 1) (hb : d266244 q = 1) : d25210 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d266244, d25210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d315, d266244, d25210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d133 q = 1) (hb : d241830 q = 1) : d25433 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d241830, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47928 q ha hb
    | true =>
      simp only [d133, d241830, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d134 q = 1) (hb : d241830 q = 1) : d25434 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d20 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d135 q = 1) (hb : d266245 q = 1) : d25435 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d266245, d25435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d135, d266245, d25435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d316 q = 1) (hb : d266246 q = 1) : d25436 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d316, d266246, d25436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d316, d266246, d25436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d317 q = 1) (hb : d266246 q = 1) : d25437 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d317, d25437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d317, d25437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d29090 q = 1) (hb : d266244 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d29090, d266244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d29090, d266244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h14 (q : Pattern) (ha : d21 q = 1) (hb : d266245 q = 1) : d21 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d29091 q = 1) (hb : d266246 q = 1) : d29112 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d29091, d266246, d29112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d29091, d266246, d29112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d29092 q = 1) (hb : d266246 q = 1) : d29113 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d29092, d29113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d29092, d29113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h17 (q : Pattern) (ha : d29100 q = 1) (hb : d266246 q = 1) : d266734 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d29100, d266734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d29100, d266734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro72966 (p : Pattern) (ha : d29107 p = 1) (hb : d266246 p = 1) : d266743 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28746 q = 1) (hb : d266246 q = 1) : d266368 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28746, d266368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72887 q ha hb
    | true =>
      simp only [d28746, d266368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28747 q = 1) (hb : d266246 q = 1) : d266369 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28747, d266369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28747, d266369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28748 q = 1) (hb : d266246 q = 1) : d266370 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28748, d266370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28748, d266370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28749 q = 1) (hb : d266246 q = 1) : d266371 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28749, d266371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28749, d266371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29101 q = 1) (hb : d266246 q = 1) : d266735 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29101, d266735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72965 q ha hb
    | true =>
      simp only [d29101, d266735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d29102 q = 1) (hb : d266246 q = 1) : d266736 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29102, d266736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29102, d266736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29103 q = 1) (hb : d266246 q = 1) : d266737 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29103, d266737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29103, d266737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d29104 q = 1) (hb : d266246 q = 1) : d266738 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29104, d266738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29104, d266738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d29105 q = 1) (hb : d266246 q = 1) : d266741 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29105, d266741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29105, d266741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29094 q = 1) (hb : d266246 q = 1) : d266735 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29094, d266735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72963 q ha hb
    | true =>
      simp only [d29094, d266735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d29095 q = 1) (hb : d266246 q = 1) : d266736 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29095, d266736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d29095, d266736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d29096 q = 1) (hb : d266246 q = 1) : d266737 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29096, d266737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29096, d266737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d29097 q = 1) (hb : d266246 q = 1) : d266738 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29097, d266738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d29097, d266738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d29106 q = 1) (hb : d266246 q = 1) : d266742 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29106, d266742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d29106, d266742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d29107 q = 1) (hb : d266246 q = 1) : d266743 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d29107, d266743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29107, d266743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro72967 (p : Pattern) (ha : d29120 p = 1) (hb : d266246 p = 1) : d266747 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29101 q = 1) (hb : d266246 q = 1) : d266735 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29101, d266735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72965 q ha hb
    | true =>
      simp only [d29101, d266735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29102 q = 1) (hb : d266246 q = 1) : d266736 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29102, d266736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d29102, d266736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d29103 q = 1) (hb : d266246 q = 1) : d266737 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29103, d266737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29103, d266737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d29104 q = 1) (hb : d266246 q = 1) : d266738 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29104, d266738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29104, d266738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29111 q = 1) (hb : d266246 q = 1) : d266742 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29111, d266742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29111, d266742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d29119 q = 1) (hb : d266246 q = 1) : d29119 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d29120 q = 1) (hb : d266246 q = 1) : d266747 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d29120, d266747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29120, d266747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro72968 (p : Pattern) (ha : d29127 p = 1) (hb : d266246 p = 1) : d266754 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29108 q = 1) (hb : d266246 q = 1) : d266744 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29108, d266744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72964 q ha hb
    | true =>
      simp only [d29108, d266744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72966 q ha hb
  have h2 (q : Pattern) (ha : d29109 q = 1) (hb : d266246 q = 1) : d266745 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29109, d266745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29109, d266745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29110 q = 1) (hb : d266246 q = 1) : d266746 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29110, d266746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29110, d266746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d29121 q = 1) (hb : d266246 q = 1) : d266748 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29121, d266748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72966 q ha hb
    | true =>
      simp only [d29121, d266748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72967 q ha hb
  have h5 (q : Pattern) (ha : d29122 q = 1) (hb : d266246 q = 1) : d266749 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29122, d266749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29122, d266749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29123 q = 1) (hb : d266246 q = 1) : d266750 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29123, d266750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29123, d266750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29124 q = 1) (hb : d266246 q = 1) : d266751 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d29124, d266751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29124, d266751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d29125 q = 1) (hb : d266246 q = 1) : d266752 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d29125, d266752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29125, d266752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d29126 q = 1) (hb : d266246 q = 1) : d266753 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d29126, d266753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29126, d266753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29127 q = 1) (hb : d266246 q = 1) : d266754 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d29127, d266754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29127, d266754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro72969 (p : Pattern) (ha : d29131 p = 1) (hb : d266246 p = 1) : d266758 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29121 q = 1) (hb : d266246 q = 1) : d266748 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29121, d266748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72966 q ha hb
    | true =>
      simp only [d29121, d266748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72967 q ha hb
  have h2 (q : Pattern) (ha : d29122 q = 1) (hb : d266246 q = 1) : d266749 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29122, d266749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29122, d266749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29123 q = 1) (hb : d266246 q = 1) : d266750 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29123, d266750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29123, d266750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d29125 q = 1) (hb : d266246 q = 1) : d266752 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d29125, d266752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29125, d266752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29130 q = 1) (hb : d266246 q = 1) : d266757 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d29130, d266757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29130, d266757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d29131 q = 1) (hb : d266246 q = 1) : d266758 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d29131, d266758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29131, d266758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72970 (p : Pattern) (ha : d29137 p = 1) (hb : d266246 p = 1) : d266764 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29128 q = 1) (hb : d266246 q = 1) : d266755 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29128, d266755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72968 q ha hb
    | true =>
      simp only [d29128, d266755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29129 q = 1) (hb : d266246 q = 1) : d266756 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29129, d266756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29129, d266756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29132 q = 1) (hb : d266246 q = 1) : d266759 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29132, d266759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72969 q ha hb
    | true =>
      simp only [d29132, d266759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29133 q = 1) (hb : d266246 q = 1) : d266760 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29133, d266760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29133, d266760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29134 q = 1) (hb : d266246 q = 1) : d266761 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29134, d266761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29134, d266761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29135 q = 1) (hb : d266246 q = 1) : d266762 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29135, d266762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29135, d266762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29136 q = 1) (hb : d266246 q = 1) : d266763 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29136, d266763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29136, d266763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d29137 q = 1) (hb : d266246 q = 1) : d266764 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29137, d266764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29137, d266764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72971 (p : Pattern) (ha : d29141 p = 1) (hb : d266246 p = 1) : d266768 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29132 q = 1) (hb : d266246 q = 1) : d266759 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29132, d266759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72969 q ha hb
    | true =>
      simp only [d29132, d266759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29133 q = 1) (hb : d266246 q = 1) : d266760 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29133, d266760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29133, d266760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29138 q = 1) (hb : d266246 q = 1) : d266765 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29138, d266765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29138, d266765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29139 q = 1) (hb : d266246 q = 1) : d266766 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29139, d266766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29139, d266766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29140 q = 1) (hb : d266246 q = 1) : d266767 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29140, d266767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29140, d266767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d29141 q = 1) (hb : d266246 q = 1) : d266768 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29141, d266768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29141, d266768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72972 (p : Pattern) (ha : d29147 p = 1) (hb : d266246 p = 1) : d266774 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29142 q = 1) (hb : d266246 q = 1) : d266769 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d29142, d266769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72970 q ha hb
    | true =>
      simp only [d29142, d266769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72971 q ha hb
  have h2 (q : Pattern) (ha : d29143 q = 1) (hb : d266246 q = 1) : d266770 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d29143, d266770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29143, d266770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29144 q = 1) (hb : d266246 q = 1) : d266771 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d29144, d266771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29144, d266771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29145 q = 1) (hb : d266246 q = 1) : d266772 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d29145, d266772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29145, d266772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29146 q = 1) (hb : d266246 q = 1) : d266773 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d29146, d266773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29146, d266773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29147 q = 1) (hb : d266246 q = 1) : d266774 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d29147, d266774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29147, d266774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72973 (p : Pattern) (ha : d29150 p = 1) (hb : d266246 p = 1) : d266777 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29128 q = 1) (hb : d266246 q = 1) : d266755 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29128, d266755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72968 q ha hb
    | true =>
      simp only [d29128, d266755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29129 q = 1) (hb : d266246 q = 1) : d266756 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29129, d266756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29129, d266756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29132 q = 1) (hb : d266246 q = 1) : d266759 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29132, d266759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72969 q ha hb
    | true =>
      simp only [d29132, d266759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29133 q = 1) (hb : d266246 q = 1) : d266760 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29133, d266760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29133, d266760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29134 q = 1) (hb : d266246 q = 1) : d266761 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29134, d266761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29134, d266761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29135 q = 1) (hb : d266246 q = 1) : d266762 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29135, d266762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29135, d266762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29136 q = 1) (hb : d266246 q = 1) : d266763 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29136, d266763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29136, d266763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d29150 q = 1) (hb : d266246 q = 1) : d266777 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29150, d266777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29150, d266777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro72974 (p : Pattern) (ha : d29151 p = 1) (hb : d266246 p = 1) : d266778 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29132 q = 1) (hb : d266246 q = 1) : d266759 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29132, d266759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72969 q ha hb
    | true =>
      simp only [d29132, d266759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29133 q = 1) (hb : d266246 q = 1) : d266760 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29133, d266760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29133, d266760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29138 q = 1) (hb : d266246 q = 1) : d266765 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29138, d266765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29138, d266765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29139 q = 1) (hb : d266246 q = 1) : d266766 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29139, d266766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29139, d266766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29140 q = 1) (hb : d266246 q = 1) : d266767 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29140, d266767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29140, d266767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d29151 q = 1) (hb : d266246 q = 1) : d266778 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29151, d266778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29151, d266778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72975 (p : Pattern) (ha : d29157 p = 1) (hb : d266246 p = 1) : d266784 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29142 q = 1) (hb : d266246 q = 1) : d266769 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d29142, d266769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72970 q ha hb
    | true =>
      simp only [d29142, d266769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72971 q ha hb
  have h2 (q : Pattern) (ha : d29143 q = 1) (hb : d266246 q = 1) : d266770 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d29143, d266770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29143, d266770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29144 q = 1) (hb : d266246 q = 1) : d266771 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d29144, d266771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29144, d266771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29145 q = 1) (hb : d266246 q = 1) : d266772 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d29145, d266772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29145, d266772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29146 q = 1) (hb : d266246 q = 1) : d266773 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d29146, d266773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29146, d266773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29152 q = 1) (hb : d266246 q = 1) : d266779 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d29152, d266779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72973 q ha hb
    | true =>
      simp only [d29152, d266779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72974 q ha hb
  have h7 (q : Pattern) (ha : d29153 q = 1) (hb : d266246 q = 1) : d266780 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d29153, d266780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29153, d266780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d29154 q = 1) (hb : d266246 q = 1) : d266781 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d29154, d266781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29154, d266781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d29155 q = 1) (hb : d266246 q = 1) : d266782 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d29155, d266782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29155, d266782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29156 q = 1) (hb : d266246 q = 1) : d266783 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d29156, d266783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29156, d266783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d29157 q = 1) (hb : d266246 q = 1) : d266784 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d29157, d266784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29157, d266784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro72976 (p : Pattern) (ha : d29339 p = 1) (hb : d266246 p = 1) : d266876 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29142 q = 1) (hb : d266246 q = 1) : d266769 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d29142, d266769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72970 q ha hb
    | true =>
      simp only [d29142, d266769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72971 q ha hb
  have h2 (q : Pattern) (ha : d29143 q = 1) (hb : d266246 q = 1) : d266770 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d29143, d266770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29143, d266770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29144 q = 1) (hb : d266246 q = 1) : d266771 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d29144, d266771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29144, d266771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29145 q = 1) (hb : d266246 q = 1) : d266772 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d29145, d266772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29145, d266772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29146 q = 1) (hb : d266246 q = 1) : d266773 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d29146, d266773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29146, d266773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29334 q = 1) (hb : d266246 q = 1) : d266871 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d29334, d266871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72971 q ha hb
    | true =>
      simp only [d29334, d266871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29335 q = 1) (hb : d266246 q = 1) : d266872 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d29335, d266872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29335, d266872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d29336 q = 1) (hb : d266246 q = 1) : d266873 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d29336, d266873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29336, d266873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d29337 q = 1) (hb : d266246 q = 1) : d266874 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d29337, d266874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29337, d266874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29338 q = 1) (hb : d266246 q = 1) : d266875 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d29338, d266875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29338, d266875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d29339 q = 1) (hb : d266246 q = 1) : d266876 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d29339, d266876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29339, d266876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro72977 (p : Pattern) (ha : d29345 p = 1) (hb : d266246 p = 1) : d266882 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29334 q = 1) (hb : d266246 q = 1) : d266871 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d29334, d266871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72971 q ha hb
    | true =>
      simp only [d29334, d266871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29335 q = 1) (hb : d266246 q = 1) : d266872 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d29335, d266872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29335, d266872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29336 q = 1) (hb : d266246 q = 1) : d266873 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d29336, d266873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29336, d266873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29337 q = 1) (hb : d266246 q = 1) : d266874 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d29337, d266874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29337, d266874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29338 q = 1) (hb : d266246 q = 1) : d266875 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d29338, d266875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29338, d266875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29340 q = 1) (hb : d266246 q = 1) : d266877 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d29340, d266877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72974 q ha hb
    | true =>
      simp only [d29340, d266877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29341 q = 1) (hb : d266246 q = 1) : d266878 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d29341, d266878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29341, d266878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d29342 q = 1) (hb : d266246 q = 1) : d266879 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d29342, d266879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29342, d266879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d29343 q = 1) (hb : d266246 q = 1) : d266880 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d29343, d266880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29343, d266880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29344 q = 1) (hb : d266246 q = 1) : d266881 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d29344, d266881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29344, d266881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d29345 q = 1) (hb : d266246 q = 1) : d266882 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d29345, d266882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29345, d266882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro72978 (p : Pattern) (ha : d29354 p = 1) (hb : d266246 p = 1) : d266891 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29340 q = 1) (hb : d266246 q = 1) : d266877 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d29340, d266877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72974 q ha hb
    | true =>
      simp only [d29340, d266877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29341 q = 1) (hb : d266246 q = 1) : d266878 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d29341, d266878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29341, d266878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29342 q = 1) (hb : d266246 q = 1) : d266879 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d29342, d266879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29342, d266879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29343 q = 1) (hb : d266246 q = 1) : d266880 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d29343, d266880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29343, d266880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29344 q = 1) (hb : d266246 q = 1) : d266881 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d29344, d266881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29344, d266881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29354 q = 1) (hb : d266246 q = 1) : d266891 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d29354, d266891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29354, d266891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72979 (p : Pattern) (ha : d29390 p = 1) (hb : d266246 p = 1) : d266919 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28794 q = 1) (hb : d266246 q = 1) : d266439 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28794, d266439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28794, d266439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72887 q ha hb
  have h2 (q : Pattern) (ha : d28746 q = 1) (hb : d266246 q = 1) : d266368 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28746, d266368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72887 q ha hb
    | true =>
      simp only [d28746, d266368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28795 q = 1) (hb : d266246 q = 1) : d266440 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28795, d266440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28795, d266440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28747 q = 1) (hb : d266246 q = 1) : d266369 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28747, d266369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28747, d266369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28796 q = 1) (hb : d266246 q = 1) : d266441 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28796, d266441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28796, d266441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28797 q = 1) (hb : d266246 q = 1) : d266442 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28797, d266442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28797, d266442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29385 q = 1) (hb : d266246 q = 1) : d266903 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29385, d266903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29385, d266903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72965 q ha hb
  have h8 (q : Pattern) (ha : d29101 q = 1) (hb : d266246 q = 1) : d266735 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29101, d266735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72965 q ha hb
    | true =>
      simp only [d29101, d266735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d29386 q = 1) (hb : d266246 q = 1) : d266904 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29386, d266904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29386, d266904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29102 q = 1) (hb : d266246 q = 1) : d266736 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29102, d266736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29102, d266736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d29387 q = 1) (hb : d266246 q = 1) : d266905 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29387, d266905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29387, d266905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d29388 q = 1) (hb : d266246 q = 1) : d266906 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29388, d266906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d29388, d266906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d29389 q = 1) (hb : d266246 q = 1) : d266918 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29389, d266918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29389, d266918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d29370 q = 1) (hb : d266246 q = 1) : d266903 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29370, d266903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29370, d266903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72963 q ha hb
  have h15 (q : Pattern) (ha : d29094 q = 1) (hb : d266246 q = 1) : d266735 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29094, d266735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72963 q ha hb
    | true =>
      simp only [d29094, d266735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d29371 q = 1) (hb : d266246 q = 1) : d266904 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29371, d266904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d29371, d266904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d29095 q = 1) (hb : d266246 q = 1) : d266736 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29095, d266736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d29095, d266736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d29372 q = 1) (hb : d266246 q = 1) : d266905 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29372, d266905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d29372, d266905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d29373 q = 1) (hb : d266246 q = 1) : d266906 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29373, d266906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d29373, d266906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d29379 q = 1) (hb : d266246 q = 1) : d266912 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29379, d266912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d29379, d266912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d29390 q = 1) (hb : d266246 q = 1) : d266919 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d29390, d266919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d29390, d266919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro72980 (p : Pattern) (ha : d29400 p = 1) (hb : d266246 p = 1) : d266923 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29385 q = 1) (hb : d266246 q = 1) : d266903 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29385, d266903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29385, d266903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72965 q ha hb
  have h2 (q : Pattern) (ha : d29101 q = 1) (hb : d266246 q = 1) : d266735 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29101, d266735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72965 q ha hb
    | true =>
      simp only [d29101, d266735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d29386 q = 1) (hb : d266246 q = 1) : d266904 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29386, d266904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d29386, d266904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d29102 q = 1) (hb : d266246 q = 1) : d266736 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29102, d266736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29102, d266736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29387 q = 1) (hb : d266246 q = 1) : d266905 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29387, d266905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29387, d266905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29388 q = 1) (hb : d266246 q = 1) : d266906 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29388, d266906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29388, d266906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29394 q = 1) (hb : d266246 q = 1) : d266912 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29394, d266912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29394, d266912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d29399 q = 1) (hb : d266246 q = 1) : d29399 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d29400 q = 1) (hb : d266246 q = 1) : d266923 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d29400, d266923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29400, d266923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro72981 (p : Pattern) (ha : d29419 p = 1) (hb : d266246 p = 1) : d266942 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29401 q = 1) (hb : d266246 q = 1) : d266924 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29401, d266924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72979 q ha hb
    | true =>
      simp only [d29401, d266924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72980 q ha hb
  have h2 (q : Pattern) (ha : d29402 q = 1) (hb : d266246 q = 1) : d266925 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29402, d266925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29402, d266925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29403 q = 1) (hb : d266246 q = 1) : d266926 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29403, d266926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29403, d266926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d29409 q = 1) (hb : d266246 q = 1) : d266932 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d29409, d266932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29409, d266932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29418 q = 1) (hb : d266246 q = 1) : d266941 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d29418, d266941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29418, d266941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d29419 q = 1) (hb : d266246 q = 1) : d266942 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d29419, d266942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29419, d266942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72982 (p : Pattern) (ha : d29505 p = 1) (hb : d266246 p = 1) : d266974 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29420 q = 1) (hb : d266246 q = 1) : d266943 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29420, d266943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72981 q ha hb
    | true =>
      simp only [d29420, d266943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29421 q = 1) (hb : d266246 q = 1) : d266944 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29421, d266944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29421, d266944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29502 q = 1) (hb : d266246 q = 1) : d266971 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29502, d266971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29502, d266971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29503 q = 1) (hb : d266246 q = 1) : d266972 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29503, d266972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29503, d266972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29504 q = 1) (hb : d266246 q = 1) : d266973 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29504, d266973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29504, d266973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d29505 q = 1) (hb : d266246 q = 1) : d266974 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29505, d266974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29505, d266974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72983 (p : Pattern) (ha : d29511 p = 1) (hb : d266246 p = 1) : d266980 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29506 q = 1) (hb : d266246 q = 1) : d266975 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d29506, d266975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72982 q ha hb
    | true =>
      simp only [d29506, d266975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29507 q = 1) (hb : d266246 q = 1) : d266976 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d29507, d266976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29507, d266976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29508 q = 1) (hb : d266246 q = 1) : d266977 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d29508, d266977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29508, d266977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29509 q = 1) (hb : d266246 q = 1) : d266978 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d29509, d266978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29509, d266978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29510 q = 1) (hb : d266246 q = 1) : d266979 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d29510, d266979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29510, d266979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29511 q = 1) (hb : d266246 q = 1) : d266980 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d29511, d266980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29511, d266980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72984 (p : Pattern) (ha : d29162 p = 1) (hb : d266246 p = 1) : d266789 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29128 q = 1) (hb : d266246 q = 1) : d266755 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29128, d266755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72968 q ha hb
    | true =>
      simp only [d29128, d266755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29129 q = 1) (hb : d266246 q = 1) : d266756 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29129, d266756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29129, d266756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29132 q = 1) (hb : d266246 q = 1) : d266759 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29132, d266759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72969 q ha hb
    | true =>
      simp only [d29132, d266759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29133 q = 1) (hb : d266246 q = 1) : d266760 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29133, d266760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29133, d266760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29134 q = 1) (hb : d266246 q = 1) : d266761 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29134, d266761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29134, d266761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29135 q = 1) (hb : d266246 q = 1) : d266762 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29135, d266762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29135, d266762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29161 q = 1) (hb : d266246 q = 1) : d266788 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29161, d266788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29161, d266788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d29162 q = 1) (hb : d266246 q = 1) : d266789 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29162, d266789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29162, d266789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72985 (p : Pattern) (ha : d29164 p = 1) (hb : d266246 p = 1) : d266791 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29132 q = 1) (hb : d266246 q = 1) : d266759 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29132, d266759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72969 q ha hb
    | true =>
      simp only [d29132, d266759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29133 q = 1) (hb : d266246 q = 1) : d266760 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29133, d266760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29133, d266760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29138 q = 1) (hb : d266246 q = 1) : d266765 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29138, d266765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29138, d266765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29139 q = 1) (hb : d266246 q = 1) : d266766 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29139, d266766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29139, d266766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29163 q = 1) (hb : d266246 q = 1) : d266790 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29163, d266790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29163, d266790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29164 q = 1) (hb : d266246 q = 1) : d266791 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29164, d266791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29164, d266791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72986 (p : Pattern) (ha : d29171 p = 1) (hb : d266246 p = 1) : d266798 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29128 q = 1) (hb : d266246 q = 1) : d266755 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29128, d266755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72968 q ha hb
    | true =>
      simp only [d29128, d266755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29129 q = 1) (hb : d266246 q = 1) : d266756 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29129, d266756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29129, d266756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29132 q = 1) (hb : d266246 q = 1) : d266759 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29132, d266759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72969 q ha hb
    | true =>
      simp only [d29132, d266759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29133 q = 1) (hb : d266246 q = 1) : d266760 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29133, d266760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29133, d266760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29134 q = 1) (hb : d266246 q = 1) : d266761 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29134, d266761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29134, d266761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29169 q = 1) (hb : d266246 q = 1) : d266796 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29169, d266796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29169, d266796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29170 q = 1) (hb : d266246 q = 1) : d266797 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29170, d266797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29170, d266797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d29171 q = 1) (hb : d266246 q = 1) : d266798 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29171, d266798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29171, d266798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72987 (p : Pattern) (ha : d29174 p = 1) (hb : d266246 p = 1) : d266801 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29132 q = 1) (hb : d266246 q = 1) : d266759 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29132, d266759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72969 q ha hb
    | true =>
      simp only [d29132, d266759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29133 q = 1) (hb : d266246 q = 1) : d266760 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29133, d266760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29133, d266760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29138 q = 1) (hb : d266246 q = 1) : d266765 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29138, d266765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29138, d266765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29172 q = 1) (hb : d266246 q = 1) : d266799 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29172, d266799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29172, d266799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29173 q = 1) (hb : d266246 q = 1) : d266800 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29173, d266800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29173, d266800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d29174 q = 1) (hb : d266246 q = 1) : d266801 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29174, d266801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29174, d266801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72988 (p : Pattern) (ha : d23694 p = 1) (hb : d266246 p = 1) : d240651 p = 1 := by
  have h0 (q : Pattern) (ha : d823 q = 1) (hb : d236581 q = 1) : d823 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d532 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d824 q = 1) (hb : d266244 q = 1) : d9759 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d824, d266244, d9759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d824, d266244, d9759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d266245 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23692 q = 1) (hb : d266246 q = 1) : d9760 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23692, d266246, d9760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23692, d266246, d9760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23693 q = 1) (hb : d266246 q = 1) : d9761 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23693, d9761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23693, d9761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d532 q = 1) (hb : d236581 q = 1) : d532 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d314 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d533 q = 1) (hb : d266244 q = 1) : d25428 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d533, d266244, d25428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d533, d266244, d25428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d23419 q = 1) (hb : d266246 q = 1) : d25781 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23419, d266246, d25781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23419, d266246, d25781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d23420 q = 1) (hb : d266246 q = 1) : d25782 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23420, d25782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23420, d25782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d23694 q = 1) (hb : d266246 q = 1) : d240651 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d23694, d240651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23694, d240651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro72989 (p : Pattern) (ha : d29181 p = 1) (hb : d266246 p = 1) : d240878 p = 1 := by
  have h0 (q : Pattern) (ha : d1201 q = 1) (hb : d236581 q = 1) : d1201 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d823 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1202 q = 1) (hb : d266244 q = 1) : d10042 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1202, d266244, d10042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1202, d266244, d10042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d266245 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d24014 q = 1) (hb : d266246 q = 1) : d10043 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d24014, d266246, d10043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24014, d266246, d10043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d24015 q = 1) (hb : d266246 q = 1) : d10044 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d24015, d10044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24015, d10044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d823 q = 1) (hb : d236581 q = 1) : d823 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d532 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d824 q = 1) (hb : d266244 q = 1) : d9759 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d824, d266244, d9759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d824, d266244, d9759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d28884 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d29178 q = 1) (hb : d266245 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d29178, d266245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d29178, d266245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d29179 q = 1) (hb : d266246 q = 1) : d9760 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d29179, d266246, d9760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29179, d266246, d9760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d29180 q = 1) (hb : d266246 q = 1) : d9761 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d29180, d9761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d29180, d9761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h15 (q : Pattern) (ha : d29181 q = 1) (hb : d266246 q = 1) : d240878 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d29181, d240878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29181, d240878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro72990 (p : Pattern) (ha : d29186 p = 1) (hb : d266246 p = 1) : d266805 p = 1 := by
  have h0 (q : Pattern) (ha : d823 q = 1) (hb : d236581 q = 1) : d823 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d532 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d824 q = 1) (hb : d266244 q = 1) : d9759 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d824, d266244, d9759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d824, d266244, d9759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d28881 q = 1) (hb : d241830 q = 1) : d28881 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d28884 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d28885 q = 1) (hb : d266245 q = 1) : d251925 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d28885, d266245, d251925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28885, d266245, d251925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d28886 q = 1) (hb : d266246 q = 1) : d266560 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d28886, d266246, d266560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28886, d266246, d266560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d28887 q = 1) (hb : d266246 q = 1) : d266561 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d28887, d266561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28887, d266561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d532 q = 1) (hb : d236581 q = 1) : d532 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d314 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d533 q = 1) (hb : d266244 q = 1) : d25428 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d533, d266244, d25428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d533, d266244, d25428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d266245 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d23419 q = 1) (hb : d266246 q = 1) : d25781 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23419, d266246, d25781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23419, d266246, d25781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d23420 q = 1) (hb : d266246 q = 1) : d25782 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23420, d25782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23420, d25782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h15 (q : Pattern) (ha : d29186 q = 1) (hb : d266246 q = 1) : d266805 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d29186, d266805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29186, d266805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro72991 (p : Pattern) (ha : d29192 p = 1) (hb : d266246 p = 1) : d266811 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29182 q = 1) (hb : d266246 q = 1) : d240879 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29182, d240879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72989 q ha hb
    | true =>
      simp only [d29182, d240879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29183 q = 1) (hb : d266246 q = 1) : d240880 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29183, d240880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d29183, d240880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d29184 q = 1) (hb : d266246 q = 1) : d240881 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29184, d240881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29184, d240881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d29185 q = 1) (hb : d266246 q = 1) : d240882 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29185, d240882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29185, d240882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29187 q = 1) (hb : d266246 q = 1) : d266806 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29187, d266806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72990 q ha hb
    | true =>
      simp only [d29187, d266806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d29188 q = 1) (hb : d266246 q = 1) : d266807 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29188, d266807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29188, d266807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29189 q = 1) (hb : d266246 q = 1) : d266808 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29189, d266808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29189, d266808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d29190 q = 1) (hb : d266246 q = 1) : d266809 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29190, d266809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29190, d266809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d29191 q = 1) (hb : d266246 q = 1) : d266810 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29191, d266810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29191, d266810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23695 q = 1) (hb : d266246 q = 1) : d240652 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23695, d240652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72988 q ha hb
    | true =>
      simp only [d23695, d240652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23696 q = 1) (hb : d266246 q = 1) : d240653 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23696, d240653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23696, d240653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d23697 q = 1) (hb : d266246 q = 1) : d240654 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23697, d240654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23697, d240654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23698 q = 1) (hb : d266246 q = 1) : d240655 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23698, d240655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23698, d240655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d23422 q = 1) (hb : d266246 q = 1) : d25784 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d25784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72935 q ha hb
    | true =>
      simp only [d23422, d25784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d23423 q = 1) (hb : d266246 q = 1) : d25785 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d25785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d23423, d25785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d23424 q = 1) (hb : d266246 q = 1) : d25786 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23424, d25786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23424, d25786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23425 q = 1) (hb : d266246 q = 1) : d25787 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23425, d25787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d23425, d25787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d23699 q = 1) (hb : d266246 q = 1) : d240656 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23699, d240656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23699, d240656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d29192 q = 1) (hb : d266246 q = 1) : d266811 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d29192, d266811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29192, d266811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro72992 (p : Pattern) (ha : d29196 p = 1) (hb : d266246 p = 1) : d266815 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23422 q = 1) (hb : d266246 q = 1) : d25784 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d25784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72935 q ha hb
    | true =>
      simp only [d23422, d25784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23423 q = 1) (hb : d266246 q = 1) : d25785 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d25785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23423, d25785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23424 q = 1) (hb : d266246 q = 1) : d25786 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23424, d25786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23424, d25786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23425 q = 1) (hb : d266246 q = 1) : d25787 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23425, d25787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23425, d25787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29094 q = 1) (hb : d266246 q = 1) : d266735 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29094, d266735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72963 q ha hb
    | true =>
      simp only [d29094, d266735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d29095 q = 1) (hb : d266246 q = 1) : d266736 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29095, d266736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29095, d266736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29096 q = 1) (hb : d266246 q = 1) : d266737 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29096, d266737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29096, d266737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d29097 q = 1) (hb : d266246 q = 1) : d266738 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29097, d266738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29097, d266738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d29098 q = 1) (hb : d266246 q = 1) : d266739 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29098, d266739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29098, d266739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29106 q = 1) (hb : d266246 q = 1) : d266742 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29106, d266742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29106, d266742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d29196 q = 1) (hb : d266246 q = 1) : d266815 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d29196, d266815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29196, d266815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro72993 (p : Pattern) (ha : d29202 p = 1) (hb : d266246 p = 1) : d266821 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29193 q = 1) (hb : d266246 q = 1) : d266812 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29193, d266812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72991 q ha hb
    | true =>
      simp only [d29193, d266812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72964 q ha hb
  have h2 (q : Pattern) (ha : d29194 q = 1) (hb : d266246 q = 1) : d266813 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29194, d266813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29194, d266813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29195 q = 1) (hb : d266246 q = 1) : d266814 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29195, d266814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29195, d266814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d29197 q = 1) (hb : d266246 q = 1) : d266816 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29197, d266816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72964 q ha hb
    | true =>
      simp only [d29197, d266816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72992 q ha hb
  have h5 (q : Pattern) (ha : d29198 q = 1) (hb : d266246 q = 1) : d266817 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29198, d266817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29198, d266817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29199 q = 1) (hb : d266246 q = 1) : d266818 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29199, d266818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29199, d266818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29200 q = 1) (hb : d266246 q = 1) : d266819 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d29200, d266819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29200, d266819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d29108 q = 1) (hb : d266246 q = 1) : d266744 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29108, d266744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72964 q ha hb
    | true =>
      simp only [d29108, d266744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72966 q ha hb
  have h9 (q : Pattern) (ha : d29109 q = 1) (hb : d266246 q = 1) : d266745 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29109, d266745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29109, d266745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29110 q = 1) (hb : d266246 q = 1) : d266746 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29110, d266746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29110, d266746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d29121 q = 1) (hb : d266246 q = 1) : d266748 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29121, d266748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72966 q ha hb
    | true =>
      simp only [d29121, d266748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72967 q ha hb
  have h12 (q : Pattern) (ha : d29122 q = 1) (hb : d266246 q = 1) : d266749 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29122, d266749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29122, d266749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d29123 q = 1) (hb : d266246 q = 1) : d266750 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29123, d266750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29123, d266750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d29124 q = 1) (hb : d266246 q = 1) : d266751 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d29124, d266751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d29124, d266751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d29201 q = 1) (hb : d266246 q = 1) : d266820 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d29201, d266820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29201, d266820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d29202 q = 1) (hb : d266246 q = 1) : d266821 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d29202, d266821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d29202, d266821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro72994 (p : Pattern) (ha : d29208 p = 1) (hb : d266246 p = 1) : d266827 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29203 q = 1) (hb : d266246 q = 1) : d266822 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29203, d266822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72993 q ha hb
    | true =>
      simp only [d29203, d266822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29204 q = 1) (hb : d266246 q = 1) : d266823 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29204, d266823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29204, d266823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29128 q = 1) (hb : d266246 q = 1) : d266755 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29128, d266755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72968 q ha hb
    | true =>
      simp only [d29128, d266755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29129 q = 1) (hb : d266246 q = 1) : d266756 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29129, d266756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29129, d266756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29205 q = 1) (hb : d266246 q = 1) : d266824 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29205, d266824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29205, d266824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29206 q = 1) (hb : d266246 q = 1) : d266825 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29206, d266825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29206, d266825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29207 q = 1) (hb : d266246 q = 1) : d266826 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29207, d266826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29207, d266826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d29208 q = 1) (hb : d266246 q = 1) : d266827 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29208, d266827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29208, d266827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72995 (p : Pattern) (ha : d29290 p = 1) (hb : d266246 p = 1) : d266830 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29101 q = 1) (hb : d266246 q = 1) : d266735 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29101, d266735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72965 q ha hb
    | true =>
      simp only [d29101, d266735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29102 q = 1) (hb : d266246 q = 1) : d266736 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29102, d266736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d29102, d266736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d29103 q = 1) (hb : d266246 q = 1) : d266737 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29103, d266737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29103, d266737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d29104 q = 1) (hb : d266246 q = 1) : d266738 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29104, d266738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29104, d266738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29111 q = 1) (hb : d266246 q = 1) : d266742 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29111, d266742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29111, d266742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d29290 q = 1) (hb : d266246 q = 1) : d266830 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d29290, d266830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29290, d266830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72996 (p : Pattern) (ha : d29296 p = 1) (hb : d266246 p = 1) : d266836 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29108 q = 1) (hb : d266246 q = 1) : d266744 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29108, d266744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72964 q ha hb
    | true =>
      simp only [d29108, d266744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72966 q ha hb
  have h2 (q : Pattern) (ha : d29109 q = 1) (hb : d266246 q = 1) : d266745 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29109, d266745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29109, d266745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29110 q = 1) (hb : d266246 q = 1) : d266746 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29110, d266746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29110, d266746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d29121 q = 1) (hb : d266246 q = 1) : d266748 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29121, d266748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72966 q ha hb
    | true =>
      simp only [d29121, d266748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72967 q ha hb
  have h5 (q : Pattern) (ha : d29122 q = 1) (hb : d266246 q = 1) : d266749 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29122, d266749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29122, d266749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29123 q = 1) (hb : d266246 q = 1) : d266750 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29123, d266750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29123, d266750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29124 q = 1) (hb : d266246 q = 1) : d266751 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d29124, d266751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29124, d266751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d29291 q = 1) (hb : d266246 q = 1) : d266831 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29291, d266831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72966 q ha hb
    | true =>
      simp only [d29291, d266831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72995 q ha hb
  have h9 (q : Pattern) (ha : d29292 q = 1) (hb : d266246 q = 1) : d266832 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29292, d266832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29292, d266832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29293 q = 1) (hb : d266246 q = 1) : d266833 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29293, d266833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29293, d266833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d29294 q = 1) (hb : d266246 q = 1) : d266834 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d29294, d266834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d29294, d266834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d29295 q = 1) (hb : d266246 q = 1) : d266835 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d29295, d266835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29295, d266835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d29296 q = 1) (hb : d266246 q = 1) : d266836 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d29296, d266836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d29296, d266836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro72997 (p : Pattern) (ha : d29302 p = 1) (hb : d266246 p = 1) : d266842 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29297 q = 1) (hb : d266246 q = 1) : d266837 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29297, d266837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72996 q ha hb
    | true =>
      simp only [d29297, d266837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29298 q = 1) (hb : d266246 q = 1) : d266838 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29298, d266838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29298, d266838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29299 q = 1) (hb : d266246 q = 1) : d266839 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29299, d266839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29299, d266839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29300 q = 1) (hb : d266246 q = 1) : d266840 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29300, d266840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29300, d266840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29301 q = 1) (hb : d266246 q = 1) : d266841 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29301, d266841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29301, d266841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d29302 q = 1) (hb : d266246 q = 1) : d266842 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29302, d266842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29302, d266842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72998 (p : Pattern) (ha : d238956 p = 1) (hb : d266246 p = 1) : d266848 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29165 q = 1) (hb : d266246 q = 1) : d266792 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d29165, d266792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72984 q ha hb
    | true =>
      simp only [d29165, d266792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72985 q ha hb
  have h2 (q : Pattern) (ha : d29166 q = 1) (hb : d266246 q = 1) : d266793 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d29166, d266793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29166, d266793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29167 q = 1) (hb : d266246 q = 1) : d266794 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d29167, d266794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29167, d266794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29168 q = 1) (hb : d266246 q = 1) : d266795 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d29168, d266795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29168, d266795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29175 q = 1) (hb : d266246 q = 1) : d266802 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d29175, d266802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72986 q ha hb
    | true =>
      simp only [d29175, d266802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72987 q ha hb
  have h6 (q : Pattern) (ha : d29176 q = 1) (hb : d266246 q = 1) : d266803 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d29176, d266803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29176, d266803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29177 q = 1) (hb : d266246 q = 1) : d266804 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d29177, d266804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29177, d266804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d29209 q = 1) (hb : d266246 q = 1) : d266828 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d29209, d266828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72994 q ha hb
    | true =>
      simp only [d29209, d266828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72970 q ha hb
  have h9 (q : Pattern) (ha : d238952 q = 1) (hb : d266246 q = 1) : d266829 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238952, d266829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d238952, d266829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d29303 q = 1) (hb : d266246 q = 1) : d266843 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d29303, d266843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72997 q ha hb
    | true =>
      simp only [d29303, d266843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d29304 q = 1) (hb : d266246 q = 1) : d266844 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d29304, d266844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d29304, d266844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d238953 q = 1) (hb : d266246 q = 1) : d266845 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238953, d266845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d238953, d266845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d238954 q = 1) (hb : d266246 q = 1) : d266846 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238954, d266846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d238954, d266846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d238955 q = 1) (hb : d266246 q = 1) : d266847 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238955, d266847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238955, d266847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d238956 q = 1) (hb : d266246 q = 1) : d266848 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238956, d266848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238956, d266848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro72999 (p : Pattern) (ha : d29309 p = 1) (hb : d266246 p = 1) : d266849 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29128 q = 1) (hb : d266246 q = 1) : d266755 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29128, d266755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72968 q ha hb
    | true =>
      simp only [d29128, d266755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29129 q = 1) (hb : d266246 q = 1) : d266756 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29129, d266756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29129, d266756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29132 q = 1) (hb : d266246 q = 1) : d266759 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29132, d266759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72969 q ha hb
    | true =>
      simp only [d29132, d266759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29133 q = 1) (hb : d266246 q = 1) : d266760 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29133, d266760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29133, d266760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29134 q = 1) (hb : d266246 q = 1) : d266761 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29134, d266761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29134, d266761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29135 q = 1) (hb : d266246 q = 1) : d266762 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29135, d266762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29135, d266762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29161 q = 1) (hb : d266246 q = 1) : d266788 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29161, d266788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29161, d266788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d29309 q = 1) (hb : d266246 q = 1) : d266849 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29309, d266849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29309, d266849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
