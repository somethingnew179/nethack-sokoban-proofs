import NetHack.Soko22Hazard87.AndIntroBlocks0002
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro750 (p : Pattern) (ha : d54544 p = 1) (hb : d54889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d802 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d800 q = 1) (hb : d51715 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d51715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro389 q ha hb
    | true =>
      simp only [d800, d51715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro390 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d951 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d801 q = 1) (hb : d51716 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d51716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d801, d51716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51717 q = 1) (hb : d53705 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51717, d53705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d51717, d53705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51718 q = 1) (hb : d53706 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51718, d53706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51718, d53706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d2567 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54543 q = 1) (hb : d54888 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54543, d54888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54543, d54888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d54544 q = 1) (hb : d54889 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54544, d54889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54544, d54889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro751 (p : Pattern) (ha : d54550 p = 1) (hb : d54895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54545 q = 1) (hb : d54890 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54545, d54890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54545, d54890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro750 q ha hb
  have h2 (q : Pattern) (ha : d54546 q = 1) (hb : d54891 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54546, d54891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54546, d54891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54547 q = 1) (hb : d54892 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54547, d54892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54547, d54892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54548 q = 1) (hb : d54893 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54548, d54893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54548, d54893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54549 q = 1) (hb : d54894 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54549, d54894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54549, d54894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54550 q = 1) (hb : d54895 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54550, d54895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54550, d54895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro752 (p : Pattern) (ha : d54554 p = 1) (hb : d54899 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1181 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1179 q = 1) (hb : d51742 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d51742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro395 q ha hb
    | true =>
      simp only [d1179, d51742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro396 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1362 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1180 q = 1) (hb : d51743 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d51743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1180, d51743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51744 q = 1) (hb : d53733 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51744, d53733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d51744, d53733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51745 q = 1) (hb : d53734 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51745, d53734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51745, d53734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d2582 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54553 q = 1) (hb : d54898 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54553, d54898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54553, d54898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d54554 q = 1) (hb : d54899 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54554, d54899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54554, d54899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro753 (p : Pattern) (ha : d54560 p = 1) (hb : d54905 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54555 q = 1) (hb : d54900 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54555, d54900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54555, d54900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro752 q ha hb
  have h2 (q : Pattern) (ha : d54556 q = 1) (hb : d54901 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54556, d54901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54556, d54901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54557 q = 1) (hb : d54902 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54557, d54902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54557, d54902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54558 q = 1) (hb : d54903 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54558, d54903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54558, d54903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54559 q = 1) (hb : d54904 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54559, d54904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54559, d54904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54560 q = 1) (hb : d54905 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54560, d54905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54560, d54905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro754 (p : Pattern) (ha : d54565 p = 1) (hb : d54910 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1642 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1640 q = 1) (hb : d51770 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d51770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro401 q ha hb
    | true =>
      simp only [d1640, d51770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro402 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1839 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1641 q = 1) (hb : d51771 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d51771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1641, d51771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51772 q = 1) (hb : d53762 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51772, d53762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d51772, d53762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51773 q = 1) (hb : d53763 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51773, d53763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51773, d53763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d2598 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54564 q = 1) (hb : d54909 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54564, d54909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54564, d54909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d54565 q = 1) (hb : d54910 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54565, d54910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54565, d54910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro755 (p : Pattern) (ha : d54571 p = 1) (hb : d54916 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54566 q = 1) (hb : d54911 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54566, d54911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54566, d54911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro754 q ha hb
  have h2 (q : Pattern) (ha : d54567 q = 1) (hb : d54912 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54567, d54912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54567, d54912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54568 q = 1) (hb : d54913 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54568, d54913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54568, d54913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54569 q = 1) (hb : d54914 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54569, d54914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54569, d54914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54570 q = 1) (hb : d54915 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54570, d54915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54570, d54915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54571 q = 1) (hb : d54916 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54571, d54916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54571, d54916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro756 (p : Pattern) (ha : d54577 p = 1) (hb : d54922 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2125 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2123 q = 1) (hb : d51799 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d51799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro407 q ha hb
    | true =>
      simp only [d2123, d51799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro408 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2317 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2124 q = 1) (hb : d51800 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d51800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2124, d51800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51801 q = 1) (hb : d53792 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51801, d53792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d51801, d53792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51802 q = 1) (hb : d53793 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51802, d53793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51802, d53793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d2615 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54576 q = 1) (hb : d54921 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54576, d54921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54576, d54921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d54577 q = 1) (hb : d54922 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54577, d54922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54577, d54922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro757 (p : Pattern) (ha : d54583 p = 1) (hb : d54928 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54578 q = 1) (hb : d54923 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54578, d54923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54578, d54923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro756 q ha hb
  have h2 (q : Pattern) (ha : d54579 q = 1) (hb : d54924 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54579, d54924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54579, d54924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54580 q = 1) (hb : d54925 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54580, d54925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54580, d54925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54581 q = 1) (hb : d54926 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54581, d54926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54581, d54926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54582 q = 1) (hb : d54927 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54582, d54927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54582, d54927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54583 q = 1) (hb : d54928 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54583, d54928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54583, d54928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro758 (p : Pattern) (ha : d54589 p = 1) (hb : d54934 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d54542 q = 1) (hb : d54887 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54542, d54887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro747 q ha hb
    | true =>
      simp only [d54542, d54887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro749 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54551 q = 1) (hb : d54896 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54551, d54896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54551, d54896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro751 q ha hb
  have h3 (q : Pattern) (ha : d54552 q = 1) (hb : d54897 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54552, d54897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54552, d54897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54561 q = 1) (hb : d54906 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54561, d54906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54561, d54906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro753 q ha hb
  have h5 (q : Pattern) (ha : d54562 q = 1) (hb : d54907 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54562, d54907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54562, d54907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54563 q = 1) (hb : d54908 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54563, d54908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54563, d54908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54572 q = 1) (hb : d54917 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54572, d54917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54572, d54917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro755 q ha hb
  have h8 (q : Pattern) (ha : d54573 q = 1) (hb : d54918 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54573, d54918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54573, d54918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54574 q = 1) (hb : d54919 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54574, d54919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54574, d54919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54575 q = 1) (hb : d54920 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54575, d54920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54575, d54920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54584 q = 1) (hb : d54929 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54584, d54929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54584, d54929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro757 q ha hb
  have h12 (q : Pattern) (ha : d54585 q = 1) (hb : d54930 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54585, d54930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54585, d54930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54586 q = 1) (hb : d54931 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54586, d54931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54586, d54931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54587 q = 1) (hb : d54932 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54587, d54932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54587, d54932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54588 q = 1) (hb : d54933 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54588, d54933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54588, d54933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54589 q = 1) (hb : d54934 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d54589, d54934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54589, d54934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro759 (p : Pattern) (ha : d54595 p = 1) (hb : d54940 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54590 q = 1) (hb : d54935 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54590, d54935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro758 q ha hb
    | true =>
      simp only [d54590, d54935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54591 q = 1) (hb : d54936 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54591, d54936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54591, d54936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54592 q = 1) (hb : d54937 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54592, d54937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54592, d54937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54593 q = 1) (hb : d54938 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54593, d54938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54593, d54938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54594 q = 1) (hb : d54939 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54594, d54939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54594, d54939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54595 q = 1) (hb : d54940 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d54595, d54940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54595, d54940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro760 (p : Pattern) (ha : d54601 p = 1) (hb : d54946 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54596 q = 1) (hb : d54941 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54596, d54941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro759 q ha hb
    | true =>
      simp only [d54596, d54941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54597 q = 1) (hb : d54942 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54597, d54942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54597, d54942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54598 q = 1) (hb : d54943 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54598, d54943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54598, d54943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54599 q = 1) (hb : d54944 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54599, d54944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54599, d54944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54600 q = 1) (hb : d54945 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54600, d54945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54600, d54945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54601 q = 1) (hb : d54946 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d54601, d54946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54601, d54946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro761 (p : Pattern) (ha : d54607 p = 1) (hb : d54952 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54602 q = 1) (hb : d54947 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54602, d54947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro760 q ha hb
    | true =>
      simp only [d54602, d54947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54603 q = 1) (hb : d54948 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54603, d54948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54603, d54948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54604 q = 1) (hb : d54949 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54604, d54949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54604, d54949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54605 q = 1) (hb : d54950 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54605, d54950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54605, d54950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54606 q = 1) (hb : d54951 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54606, d54951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54606, d54951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54607 q = 1) (hb : d54952 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d54607, d54952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54607, d54952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro762 (p : Pattern) (ha : d54613 p = 1) (hb : d54958 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54608 q = 1) (hb : d54953 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54608, d54953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro761 q ha hb
    | true =>
      simp only [d54608, d54953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54609 q = 1) (hb : d54954 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54609, d54954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54609, d54954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54610 q = 1) (hb : d54955 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54610, d54955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54610, d54955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54611 q = 1) (hb : d54956 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54611, d54956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54611, d54956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54612 q = 1) (hb : d54957 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54612, d54957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54612, d54957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54613 q = 1) (hb : d54958 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d54613, d54958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54613, d54958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro763 (p : Pattern) (ha : d54619 p = 1) (hb : d54964 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54614 q = 1) (hb : d54959 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54614, d54959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro762 q ha hb
    | true =>
      simp only [d54614, d54959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54615 q = 1) (hb : d54960 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54615, d54960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54615, d54960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54616 q = 1) (hb : d54961 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54616, d54961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54616, d54961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54617 q = 1) (hb : d54962 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54617, d54962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54617, d54962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54618 q = 1) (hb : d54963 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54618, d54963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54618, d54963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54619 q = 1) (hb : d54964 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d54619, d54964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54619, d54964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro764 (p : Pattern) (ha : d54625 p = 1) (hb : d54970 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54620 q = 1) (hb : d54965 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54620, d54965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro763 q ha hb
    | true =>
      simp only [d54620, d54965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54621 q = 1) (hb : d54966 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54621, d54966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54621, d54966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54622 q = 1) (hb : d54967 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54622, d54967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54622, d54967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54623 q = 1) (hb : d54968 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54623, d54968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54623, d54968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54624 q = 1) (hb : d54969 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54624, d54969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54624, d54969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54625 q = 1) (hb : d54970 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54625, d54970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54625, d54970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro765 (p : Pattern) (ha : d54631 p = 1) (hb : d54976 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54626 q = 1) (hb : d54971 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54626, d54971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro764 q ha hb
    | true =>
      simp only [d54626, d54971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54627 q = 1) (hb : d54972 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54627, d54972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54627, d54972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54628 q = 1) (hb : d54973 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54628, d54973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54628, d54973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54629 q = 1) (hb : d54974 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54629, d54974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54629, d54974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54630 q = 1) (hb : d54975 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54630, d54975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54630, d54975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54631 q = 1) (hb : d54976 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54631, d54976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54631, d54976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro766 (p : Pattern) (ha : d54631 p = 1) (hb : d55749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54628 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d55746 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54629 q = 1) (hb : d55748 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54629, d55748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54629, d55748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54630 q = 1) (hb : d55749 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54630, d55749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54630, d55749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d55749 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54631 q = 1) (hb : d55749 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro767 (p : Pattern) (ha : d0 p = 1) (hb : d1 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro768 (p : Pattern) (ha : d54976 p = 1) (hb : d55749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54973 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d55746 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54974 q = 1) (hb : d55748 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54974, d55748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54974, d55748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54975 q = 1) (hb : d55749 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54975, d55749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54975, d55749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d55749 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54976 q = 1) (hb : d55749 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro769 (p : Pattern) (ha : d0 p = 1) (hb : d0 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro770 (p : Pattern) (ha : d2520 p = 1) (hb : d55754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d59 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59, d55754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59, d55754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2519 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2520 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro771 (p : Pattern) (ha : d54520 p = 1) (hb : d55754 p = 1) : d2898 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d114 q = 1) : d114 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51649 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51650 q = 1) (hb : d55754 q = 1) : d2896 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51650, d55754, d2896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51650, d55754, d2896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d2528 q = 1) (hb : d55754 q = 1) : d2528 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54519 q = 1) (hb : d55754 q = 1) : d2897 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54519, d2897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54519, d2897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54520 q = 1) (hb : d55754 q = 1) : d2898 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54520, d2898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54520, d2898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro772 (p : Pattern) (ha : d54527 p = 1) (hb : d55754 p = 1) : d2906 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d294 q = 1) : d294 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51666 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51667 q = 1) (hb : d55754 q = 1) : d2904 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51667, d55754, d2904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51667, d55754, d2904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d2540 q = 1) (hb : d55754 q = 1) : d2540 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54526 q = 1) (hb : d55754 q = 1) : d2905 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54526, d2905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54526, d2905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54527 q = 1) (hb : d55754 q = 1) : d2906 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54527, d2906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54527, d2906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro773 (p : Pattern) (ha : d54533 p = 1) (hb : d55754 p = 1) : d2912 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2521 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro770 q ha hb
  have h2 (q : Pattern) (ha : d2522 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2523 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2524 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54521 q = 1) (hb : d55754 q = 1) : d2899 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54521, d2899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54521, d2899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro771 q ha hb
  have h6 (q : Pattern) (ha : d54522 q = 1) (hb : d55754 q = 1) : d2900 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54522, d2900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54522, d2900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54523 q = 1) (hb : d55754 q = 1) : d2901 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54523, d2901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54523, d2901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54524 q = 1) (hb : d55754 q = 1) : d2902 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54524, d2902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54524, d2902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54525 q = 1) (hb : d55754 q = 1) : d2903 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54525, d2903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54525, d2903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54528 q = 1) (hb : d55754 q = 1) : d2907 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54528, d2907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54528, d2907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro772 q ha hb
  have h11 (q : Pattern) (ha : d54529 q = 1) (hb : d55754 q = 1) : d2908 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54529, d2908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54529, d2908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54530 q = 1) (hb : d55754 q = 1) : d2909 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54530, d2909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54530, d2909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54531 q = 1) (hb : d55754 q = 1) : d2910 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54531, d2910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54531, d2910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54532 q = 1) (hb : d55754 q = 1) : d2911 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54532, d2911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54532, d2911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54533 q = 1) (hb : d55754 q = 1) : d2912 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54533, d2912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d54533, d2912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro774 (p : Pattern) (ha : d54535 p = 1) (hb : d55754 p = 1) : d2915 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d510 q = 1) : d510 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51691 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51692 q = 1) (hb : d55754 q = 1) : d2913 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51692, d55754, d2913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51692, d55754, d2913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d2553 q = 1) (hb : d55754 q = 1) : d2553 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54534 q = 1) (hb : d55754 q = 1) : d2914 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54534, d2914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54534, d2914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54535 q = 1) (hb : d55754 q = 1) : d2915 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54535, d2915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54535, d2915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro775 (p : Pattern) (ha : d54541 p = 1) (hb : d55754 p = 1) : d2921 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54536 q = 1) (hb : d55754 q = 1) : d2916 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54536, d2916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54536, d2916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro774 q ha hb
  have h2 (q : Pattern) (ha : d54537 q = 1) (hb : d55754 q = 1) : d2917 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54537, d2917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54537, d2917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54538 q = 1) (hb : d55754 q = 1) : d2918 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54538, d2918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54538, d2918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54539 q = 1) (hb : d55754 q = 1) : d2919 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54539, d2919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54539, d2919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54540 q = 1) (hb : d55754 q = 1) : d2920 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54540, d2920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54540, d2920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54541 q = 1) (hb : d55754 q = 1) : d2921 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54541, d2921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54541, d2921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro776 (p : Pattern) (ha : d54544 p = 1) (hb : d55754 p = 1) : d2925 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d802 q = 1) : d802 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51717 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51718 q = 1) (hb : d55754 q = 1) : d2923 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51718, d55754, d2923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51718, d55754, d2923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d2567 q = 1) (hb : d55754 q = 1) : d2567 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54543 q = 1) (hb : d55754 q = 1) : d2924 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54543, d2924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54543, d2924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54544 q = 1) (hb : d55754 q = 1) : d2925 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54544, d2925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54544, d2925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro777 (p : Pattern) (ha : d54550 p = 1) (hb : d55754 p = 1) : d2931 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54545 q = 1) (hb : d55754 q = 1) : d2926 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54545, d2926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54545, d2926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro776 q ha hb
  have h2 (q : Pattern) (ha : d54546 q = 1) (hb : d55754 q = 1) : d2927 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54546, d2927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54546, d2927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54547 q = 1) (hb : d55754 q = 1) : d2928 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54547, d2928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54547, d2928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54548 q = 1) (hb : d55754 q = 1) : d2929 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54548, d2929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54548, d2929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54549 q = 1) (hb : d55754 q = 1) : d2930 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54549, d2930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54549, d2930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54550 q = 1) (hb : d55754 q = 1) : d2931 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54550, d2931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54550, d2931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro778 (p : Pattern) (ha : d54554 p = 1) (hb : d55754 p = 1) : d2936 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1181 q = 1) : d1181 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51744 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51745 q = 1) (hb : d55754 q = 1) : d2934 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51745, d55754, d2934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51745, d55754, d2934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d2582 q = 1) (hb : d55754 q = 1) : d2582 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54553 q = 1) (hb : d55754 q = 1) : d2935 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54553, d2935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54553, d2935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54554 q = 1) (hb : d55754 q = 1) : d2936 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54554, d2936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54554, d2936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro779 (p : Pattern) (ha : d54560 p = 1) (hb : d55754 p = 1) : d2942 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54555 q = 1) (hb : d55754 q = 1) : d2937 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54555, d2937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54555, d2937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro778 q ha hb
  have h2 (q : Pattern) (ha : d54556 q = 1) (hb : d55754 q = 1) : d2938 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54556, d2938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54556, d2938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54557 q = 1) (hb : d55754 q = 1) : d2939 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54557, d2939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54557, d2939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54558 q = 1) (hb : d55754 q = 1) : d2940 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54558, d2940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54558, d2940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54559 q = 1) (hb : d55754 q = 1) : d2941 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54559, d2941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54559, d2941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54560 q = 1) (hb : d55754 q = 1) : d2942 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54560, d2942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54560, d2942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro780 (p : Pattern) (ha : d54565 p = 1) (hb : d55754 p = 1) : d2948 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1642 q = 1) : d1642 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51772 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51773 q = 1) (hb : d55754 q = 1) : d2946 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51773, d55754, d2946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51773, d55754, d2946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d2598 q = 1) (hb : d55754 q = 1) : d2598 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54564 q = 1) (hb : d55754 q = 1) : d2947 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54564, d2947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54564, d2947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54565 q = 1) (hb : d55754 q = 1) : d2948 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54565, d2948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54565, d2948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro781 (p : Pattern) (ha : d54571 p = 1) (hb : d55754 p = 1) : d2954 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54566 q = 1) (hb : d55754 q = 1) : d2949 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54566, d2949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54566, d2949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro780 q ha hb
  have h2 (q : Pattern) (ha : d54567 q = 1) (hb : d55754 q = 1) : d2950 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54567, d2950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54567, d2950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54568 q = 1) (hb : d55754 q = 1) : d2951 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54568, d2951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54568, d2951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54569 q = 1) (hb : d55754 q = 1) : d2952 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54569, d2952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54569, d2952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54570 q = 1) (hb : d55754 q = 1) : d2953 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54570, d2953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54570, d2953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54571 q = 1) (hb : d55754 q = 1) : d2954 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54571, d2954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54571, d2954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro782 (p : Pattern) (ha : d54577 p = 1) (hb : d55754 p = 1) : d2961 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2125 q = 1) : d2125 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51801 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51802 q = 1) (hb : d55754 q = 1) : d2959 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51802, d55754, d2959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51802, d55754, d2959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d2615 q = 1) (hb : d55754 q = 1) : d2615 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54576 q = 1) (hb : d55754 q = 1) : d2960 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54576, d2960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54576, d2960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54577 q = 1) (hb : d55754 q = 1) : d2961 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54577, d2961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54577, d2961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro783 (p : Pattern) (ha : d54583 p = 1) (hb : d55754 p = 1) : d2967 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54578 q = 1) (hb : d55754 q = 1) : d2962 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54578, d2962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54578, d2962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro782 q ha hb
  have h2 (q : Pattern) (ha : d54579 q = 1) (hb : d55754 q = 1) : d2963 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54579, d2963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54579, d2963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54580 q = 1) (hb : d55754 q = 1) : d2964 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54580, d2964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54580, d2964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54581 q = 1) (hb : d55754 q = 1) : d2965 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54581, d2965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54581, d2965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54582 q = 1) (hb : d55754 q = 1) : d2966 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54582, d2966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54582, d2966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54583 q = 1) (hb : d55754 q = 1) : d2967 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54583, d2967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54583, d2967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro784 (p : Pattern) (ha : d54589 p = 1) (hb : d55754 p = 1) : d2973 p = 1 := by
  have h0 (q : Pattern) (ha : d54542 q = 1) (hb : d55754 q = 1) : d2922 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54542, d2922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro773 q ha hb
    | true =>
      simp only [d54542, d2922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro775 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54551 q = 1) (hb : d55754 q = 1) : d2932 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54551, d2932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54551, d2932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro777 q ha hb
  have h3 (q : Pattern) (ha : d54552 q = 1) (hb : d55754 q = 1) : d2933 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54552, d2933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54552, d2933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54561 q = 1) (hb : d55754 q = 1) : d2943 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54561, d2943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54561, d2943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro779 q ha hb
  have h5 (q : Pattern) (ha : d54562 q = 1) (hb : d55754 q = 1) : d2944 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54562, d2944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54562, d2944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54563 q = 1) (hb : d55754 q = 1) : d2945 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54563, d2945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54563, d2945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54572 q = 1) (hb : d55754 q = 1) : d2955 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54572, d2955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54572, d2955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro781 q ha hb
  have h8 (q : Pattern) (ha : d54573 q = 1) (hb : d55754 q = 1) : d2956 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54573, d2956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54573, d2956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54574 q = 1) (hb : d55754 q = 1) : d2957 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54574, d2957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54574, d2957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54575 q = 1) (hb : d55754 q = 1) : d2958 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54575, d2958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54575, d2958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54584 q = 1) (hb : d55754 q = 1) : d2968 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54584, d2968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54584, d2968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro783 q ha hb
  have h12 (q : Pattern) (ha : d54585 q = 1) (hb : d55754 q = 1) : d2969 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54585, d2969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54585, d2969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54586 q = 1) (hb : d55754 q = 1) : d2970 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54586, d2970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54586, d2970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54587 q = 1) (hb : d55754 q = 1) : d2971 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54587, d2971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54587, d2971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54588 q = 1) (hb : d55754 q = 1) : d2972 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54588, d2972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54588, d2972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54589 q = 1) (hb : d55754 q = 1) : d2973 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d54589, d2973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54589, d2973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro785 (p : Pattern) (ha : d54595 p = 1) (hb : d55754 p = 1) : d2979 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54590 q = 1) (hb : d55754 q = 1) : d2974 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54590, d2974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro784 q ha hb
    | true =>
      simp only [d54590, d2974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54591 q = 1) (hb : d55754 q = 1) : d2975 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54591, d2975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54591, d2975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54592 q = 1) (hb : d55754 q = 1) : d2976 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54592, d2976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54592, d2976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54593 q = 1) (hb : d55754 q = 1) : d2977 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54593, d2977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54593, d2977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54594 q = 1) (hb : d55754 q = 1) : d2978 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54594, d2978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54594, d2978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54595 q = 1) (hb : d55754 q = 1) : d2979 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d54595, d2979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54595, d2979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro786 (p : Pattern) (ha : d54601 p = 1) (hb : d55754 p = 1) : d2985 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54596 q = 1) (hb : d55754 q = 1) : d2980 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54596, d2980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro785 q ha hb
    | true =>
      simp only [d54596, d2980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54597 q = 1) (hb : d55754 q = 1) : d2981 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54597, d2981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54597, d2981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54598 q = 1) (hb : d55754 q = 1) : d2982 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54598, d2982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54598, d2982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54599 q = 1) (hb : d55754 q = 1) : d2983 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54599, d2983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54599, d2983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54600 q = 1) (hb : d55754 q = 1) : d2984 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54600, d2984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54600, d2984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54601 q = 1) (hb : d55754 q = 1) : d2985 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d54601, d2985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54601, d2985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro787 (p : Pattern) (ha : d54607 p = 1) (hb : d55754 p = 1) : d2991 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54602 q = 1) (hb : d55754 q = 1) : d2986 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54602, d2986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro786 q ha hb
    | true =>
      simp only [d54602, d2986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54603 q = 1) (hb : d55754 q = 1) : d2987 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54603, d2987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54603, d2987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54604 q = 1) (hb : d55754 q = 1) : d2988 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54604, d2988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54604, d2988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54605 q = 1) (hb : d55754 q = 1) : d2989 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54605, d2989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54605, d2989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54606 q = 1) (hb : d55754 q = 1) : d2990 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54606, d2990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54606, d2990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54607 q = 1) (hb : d55754 q = 1) : d2991 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d54607, d2991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54607, d2991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro788 (p : Pattern) (ha : d54613 p = 1) (hb : d55754 p = 1) : d2997 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54608 q = 1) (hb : d55754 q = 1) : d2992 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54608, d2992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro787 q ha hb
    | true =>
      simp only [d54608, d2992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54609 q = 1) (hb : d55754 q = 1) : d2993 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54609, d2993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54609, d2993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54610 q = 1) (hb : d55754 q = 1) : d2994 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54610, d2994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54610, d2994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54611 q = 1) (hb : d55754 q = 1) : d2995 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54611, d2995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54611, d2995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54612 q = 1) (hb : d55754 q = 1) : d2996 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54612, d2996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54612, d2996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54613 q = 1) (hb : d55754 q = 1) : d2997 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d54613, d2997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54613, d2997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro789 (p : Pattern) (ha : d54619 p = 1) (hb : d55754 p = 1) : d3003 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54614 q = 1) (hb : d55754 q = 1) : d2998 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54614, d2998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro788 q ha hb
    | true =>
      simp only [d54614, d2998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54615 q = 1) (hb : d55754 q = 1) : d2999 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54615, d2999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54615, d2999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54616 q = 1) (hb : d55754 q = 1) : d3000 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54616, d3000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54616, d3000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54617 q = 1) (hb : d55754 q = 1) : d3001 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54617, d3001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54617, d3001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54618 q = 1) (hb : d55754 q = 1) : d3002 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54618, d3002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54618, d3002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54619 q = 1) (hb : d55754 q = 1) : d3003 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d54619, d3003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54619, d3003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro790 (p : Pattern) (ha : d54625 p = 1) (hb : d55754 p = 1) : d3009 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54620 q = 1) (hb : d55754 q = 1) : d3004 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54620, d3004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro789 q ha hb
    | true =>
      simp only [d54620, d3004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54621 q = 1) (hb : d55754 q = 1) : d3005 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54621, d3005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54621, d3005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54622 q = 1) (hb : d55754 q = 1) : d3006 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54622, d3006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54622, d3006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54623 q = 1) (hb : d55754 q = 1) : d3007 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54623, d3007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54623, d3007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54624 q = 1) (hb : d55754 q = 1) : d3008 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54624, d3008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54624, d3008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54625 q = 1) (hb : d55754 q = 1) : d3009 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54625, d3009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54625, d3009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro791 (p : Pattern) (ha : d54631 p = 1) (hb : d55757 p = 1) : d3015 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54626 q = 1) (hb : d55754 q = 1) : d3010 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54626, d3010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro790 q ha hb
    | true =>
      simp only [d54626, d3010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54627 q = 1) (hb : d55754 q = 1) : d3011 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54627, d3011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54627, d3011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54628 q = 1) (hb : d55754 q = 1) : d3012 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54628, d3012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54628, d3012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d54629 q = 1) (hb : d55756 q = 1) : d3013 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54629, d55756, d3013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54629, d55756, d3013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d54630 q = 1) (hb : d55757 q = 1) : d3014 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54630, d55757, d3014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54630, d55757, d3014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d55757 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d54631 q = 1) (hb : d55757 q = 1) : d3015 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54631, d3015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54631, d3015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro792 (p : Pattern) (ha : d2898 p = 1) (hb : d55760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d51957 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, d51957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, d51957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d51958 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, d51958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, d51958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d51964 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d51964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15 q ha hb
    | true =>
      simp only [d112, d51964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d51965 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d51965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, d51965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, d51966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, d51966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2896 q = 1) (hb : d55758 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2896, d55758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2896, d55758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2525 q = 1) (hb : d55598 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2525, d55598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2525, d55598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17 q ha hb
  have h8 (q : Pattern) (ha : d2526 q = 1) (hb : d55599 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2526, d55599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2526, d55599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2527 q = 1) (hb : d55600 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2527, d55600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2527, d55600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d2528 q = 1) (hb : d55601 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2528, d55601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2528, d55601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d2897 q = 1) (hb : d55759 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2897, d55759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2897, d55759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2898 q = 1) (hb : d55760 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2898, d55760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2898, d55760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro793 (p : Pattern) (ha : d2906 p = 1) (hb : d55768 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d52084 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, d52084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, d52084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36 q ha hb
  have h2 (q : Pattern) (ha : d286 q = 1) (hb : d52085 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, d52085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, d52085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d292 q = 1) (hb : d52091 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d52091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36 q ha hb
    | true =>
      simp only [d292, d52091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37 q ha hb
  have h4 (q : Pattern) (ha : d293 q = 1) (hb : d52092 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d52092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293, d52092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d294 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, d52093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d294, d52093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2904 q = 1) (hb : d55766 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2904, d55766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2904, d55766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2537 q = 1) (hb : d55610 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2537, d55610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2537, d55610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro697 q ha hb
  have h8 (q : Pattern) (ha : d2538 q = 1) (hb : d55611 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2538, d55611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2538, d55611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2539 q = 1) (hb : d55612 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2539, d55612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2539, d55612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d2540 q = 1) (hb : d55613 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2540, d55613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2540, d55613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d2905 q = 1) (hb : d55767 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2905, d55767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2905, d55767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2906 q = 1) (hb : d55768 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2906, d55768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2906, d55768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro794 (p : Pattern) (ha : d2912 p = 1) (hb : d55774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2899 q = 1) (hb : d55761 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2899, d55761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2899, d55761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro792 q ha hb
  have h2 (q : Pattern) (ha : d2900 q = 1) (hb : d55762 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2900, d55762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2900, d55762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2901 q = 1) (hb : d55763 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2901, d55763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2901, d55763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2902 q = 1) (hb : d55764 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2902, d55764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2902, d55764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2903 q = 1) (hb : d55765 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2903, d55765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2903, d55765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2907 q = 1) (hb : d55769 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2907, d55769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2907, d55769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro793 q ha hb
  have h7 (q : Pattern) (ha : d2908 q = 1) (hb : d55770 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2908, d55770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2908, d55770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2909 q = 1) (hb : d55771 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2909, d55771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2909, d55771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2910 q = 1) (hb : d55772 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2910, d55772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2910, d55772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2911 q = 1) (hb : d55773 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2911, d55773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2911, d55773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2912 q = 1) (hb : d55774 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2912, d55774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2912, d55774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro795 (p : Pattern) (ha : d2915 p = 1) (hb : d55777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d498 q = 1) (hb : d52245 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d498, d52245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d498, d52245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64 q ha hb
  have h2 (q : Pattern) (ha : d499 q = 1) (hb : d52246 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d499, d52246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d499, d52246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d508 q = 1) (hb : d52255 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d52255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64 q ha hb
    | true =>
      simp only [d508, d52255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67 q ha hb
  have h4 (q : Pattern) (ha : d509 q = 1) (hb : d52256 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d52256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d509, d52256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d510 q = 1) (hb : d52257 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d510, d52257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d510, d52257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2913 q = 1) (hb : d55775 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2913, d55775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2913, d55775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2550 q = 1) (hb : d55623 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2550, d55623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2550, d55623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro700 q ha hb
  have h8 (q : Pattern) (ha : d2551 q = 1) (hb : d55624 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2551, d55624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2551, d55624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2552 q = 1) (hb : d55625 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2552, d55625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2552, d55625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d2553 q = 1) (hb : d55626 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2553, d55626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2553, d55626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d2914 q = 1) (hb : d55776 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2914, d55776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2914, d55776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2915 q = 1) (hb : d55777 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2915, d55777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2915, d55777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro796 (p : Pattern) (ha : d2921 p = 1) (hb : d55783 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2916 q = 1) (hb : d55778 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2916, d55778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2916, d55778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro795 q ha hb
  have h2 (q : Pattern) (ha : d2917 q = 1) (hb : d55779 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2917, d55779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2917, d55779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2918 q = 1) (hb : d55780 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2918, d55780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2918, d55780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2919 q = 1) (hb : d55781 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2919, d55781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2919, d55781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2920 q = 1) (hb : d55782 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2920, d55782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2920, d55782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2921 q = 1) (hb : d55783 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2921, d55783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2921, d55783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro797 (p : Pattern) (ha : d2925 p = 1) (hb : d55787 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d790 q = 1) (hb : d52467 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d790, d52467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d790, d52467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108 q ha hb
  have h2 (q : Pattern) (ha : d791 q = 1) (hb : d52468 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d791, d52468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d791, d52468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d800 q = 1) (hb : d52477 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d52477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108 q ha hb
    | true =>
      simp only [d800, d52477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro111 q ha hb
  have h4 (q : Pattern) (ha : d801 q = 1) (hb : d52478 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d52478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d801, d52478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d802 q = 1) (hb : d52479 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d802, d52479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d802, d52479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2923 q = 1) (hb : d55785 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2923, d55785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2923, d55785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2564 q = 1) (hb : d55637 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2564, d55637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2564, d55637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro703 q ha hb
  have h8 (q : Pattern) (ha : d2565 q = 1) (hb : d55638 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2565, d55638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2565, d55638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2566 q = 1) (hb : d55639 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2566, d55639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2566, d55639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d2567 q = 1) (hb : d55640 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2567, d55640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2567, d55640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d2924 q = 1) (hb : d55786 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2924, d55786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2924, d55786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2925 q = 1) (hb : d55787 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2925, d55787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2925, d55787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro798 (p : Pattern) (ha : d2931 p = 1) (hb : d55793 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2926 q = 1) (hb : d55788 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2926, d55788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2926, d55788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro797 q ha hb
  have h2 (q : Pattern) (ha : d2927 q = 1) (hb : d55789 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2927, d55789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2927, d55789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2928 q = 1) (hb : d55790 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2928, d55790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2928, d55790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2929 q = 1) (hb : d55791 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2929, d55791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2929, d55791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2930 q = 1) (hb : d55792 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2930, d55792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2930, d55792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2931 q = 1) (hb : d55793 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2931, d55793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2931, d55793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro799 (p : Pattern) (ha : d2936 p = 1) (hb : d55798 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1169 q = 1) (hb : d52750 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1169, d52750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1169, d52750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro160 q ha hb
  have h2 (q : Pattern) (ha : d1170 q = 1) (hb : d52751 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1170, d52751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1170, d52751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1179 q = 1) (hb : d52760 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d52760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro160 q ha hb
    | true =>
      simp only [d1179, d52760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro163 q ha hb
  have h4 (q : Pattern) (ha : d1180 q = 1) (hb : d52761 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d52761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1180, d52761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1181 q = 1) (hb : d52762 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1181, d52762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1181, d52762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2934 q = 1) (hb : d55796 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2934, d55796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2934, d55796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2579 q = 1) (hb : d55652 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2579, d55652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2579, d55652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro706 q ha hb
  have h8 (q : Pattern) (ha : d2580 q = 1) (hb : d55653 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2580, d55653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2580, d55653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2581 q = 1) (hb : d55654 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2581, d55654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2581, d55654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d2582 q = 1) (hb : d55655 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2582, d55655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2582, d55655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d2935 q = 1) (hb : d55797 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2935, d55797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2935, d55797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2936 q = 1) (hb : d55798 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2936, d55798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2936, d55798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro800 (p : Pattern) (ha : d2942 p = 1) (hb : d55804 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2937 q = 1) (hb : d55799 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2937, d55799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2937, d55799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro799 q ha hb
  have h2 (q : Pattern) (ha : d2938 q = 1) (hb : d55800 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2938, d55800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2938, d55800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2939 q = 1) (hb : d55801 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2939, d55801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2939, d55801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2940 q = 1) (hb : d55802 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2940, d55802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2940, d55802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2941 q = 1) (hb : d55803 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2941, d55803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2941, d55803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2942 q = 1) (hb : d55804 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2942, d55804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2942, d55804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro801 (p : Pattern) (ha : d2948 p = 1) (hb : d55810 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1630 q = 1) (hb : d53071 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1630, d53071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1630, d53071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro218 q ha hb
  have h2 (q : Pattern) (ha : d1631 q = 1) (hb : d53072 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1631, d53072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1631, d53072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1640 q = 1) (hb : d53081 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d53081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro218 q ha hb
    | true =>
      simp only [d1640, d53081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro221 q ha hb
  have h4 (q : Pattern) (ha : d1641 q = 1) (hb : d53082 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d53082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1641, d53082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1642 q = 1) (hb : d53083 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1642, d53083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1642, d53083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2946 q = 1) (hb : d55808 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2946, d55808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2946, d55808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2595 q = 1) (hb : d55668 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2595, d55668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2595, d55668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro709 q ha hb
  have h8 (q : Pattern) (ha : d2596 q = 1) (hb : d55669 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2596, d55669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2596, d55669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2597 q = 1) (hb : d55670 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2597, d55670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2597, d55670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d2598 q = 1) (hb : d55671 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2598, d55671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2598, d55671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d2947 q = 1) (hb : d55809 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2947, d55809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2947, d55809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2948 q = 1) (hb : d55810 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2948, d55810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2948, d55810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro802 (p : Pattern) (ha : d2954 p = 1) (hb : d55816 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2949 q = 1) (hb : d55811 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2949, d55811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2949, d55811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro801 q ha hb
  have h2 (q : Pattern) (ha : d2950 q = 1) (hb : d55812 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2950, d55812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2950, d55812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2951 q = 1) (hb : d55813 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2951, d55813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2951, d55813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2952 q = 1) (hb : d55814 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2952, d55814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2952, d55814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2953 q = 1) (hb : d55815 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2953, d55815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2953, d55815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2954 q = 1) (hb : d55816 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2954, d55816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2954, d55816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro803 (p : Pattern) (ha : d2961 p = 1) (hb : d55823 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2113 q = 1) (hb : d53392 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2113, d53392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2113, d53392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro277 q ha hb
  have h2 (q : Pattern) (ha : d2114 q = 1) (hb : d53393 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2114, d53393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2114, d53393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2123 q = 1) (hb : d53402 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d53402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro277 q ha hb
    | true =>
      simp only [d2123, d53402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro280 q ha hb
  have h4 (q : Pattern) (ha : d2124 q = 1) (hb : d53403 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d53403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2124, d53403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2125 q = 1) (hb : d53404 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2125, d53404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2125, d53404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2959 q = 1) (hb : d55821 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2959, d55821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2959, d55821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2612 q = 1) (hb : d55685 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2612, d55685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2612, d55685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro712 q ha hb
  have h8 (q : Pattern) (ha : d2613 q = 1) (hb : d55686 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2613, d55686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2613, d55686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2614 q = 1) (hb : d55687 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2614, d55687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2614, d55687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d2615 q = 1) (hb : d55688 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2615, d55688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2615, d55688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d2960 q = 1) (hb : d55822 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2960, d55822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2960, d55822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2961 q = 1) (hb : d55823 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2961, d55823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2961, d55823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro804 (p : Pattern) (ha : d2967 p = 1) (hb : d55829 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2962 q = 1) (hb : d55824 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2962, d55824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2962, d55824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro803 q ha hb
  have h2 (q : Pattern) (ha : d2963 q = 1) (hb : d55825 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2963, d55825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2963, d55825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2964 q = 1) (hb : d55826 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2964, d55826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2964, d55826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2965 q = 1) (hb : d55827 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2965, d55827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2965, d55827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2966 q = 1) (hb : d55828 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2966, d55828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2966, d55828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2967 q = 1) (hb : d55829 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2967, d55829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2967, d55829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro805 (p : Pattern) (ha : d2973 p = 1) (hb : d55835 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d2922 q = 1) (hb : d55784 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2922, d55784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro794 q ha hb
    | true =>
      simp only [d2922, d55784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro796 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2932 q = 1) (hb : d55794 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2932, d55794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2932, d55794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro798 q ha hb
  have h3 (q : Pattern) (ha : d2933 q = 1) (hb : d55795 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d2933, d55795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2933, d55795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2943 q = 1) (hb : d55805 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2943, d55805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2943, d55805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro800 q ha hb
  have h5 (q : Pattern) (ha : d2944 q = 1) (hb : d55806 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d2944, d55806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2944, d55806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2945 q = 1) (hb : d55807 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d2945, d55807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2945, d55807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2955 q = 1) (hb : d55817 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2955, d55817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2955, d55817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro802 q ha hb
  have h8 (q : Pattern) (ha : d2956 q = 1) (hb : d55818 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d2956, d55818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2956, d55818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2957 q = 1) (hb : d55819 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d2957, d55819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2957, d55819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2958 q = 1) (hb : d55820 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d2958, d55820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2958, d55820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2968 q = 1) (hb : d55830 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2968, d55830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2968, d55830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro804 q ha hb
  have h12 (q : Pattern) (ha : d2969 q = 1) (hb : d55831 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d2969, d55831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2969, d55831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d2970 q = 1) (hb : d55832 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d2970, d55832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2970, d55832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d2971 q = 1) (hb : d55833 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d2971, d55833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2971, d55833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d2972 q = 1) (hb : d55834 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d2972, d55834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2972, d55834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d2973 q = 1) (hb : d55835 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d2973, d55835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d2973, d55835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro806 (p : Pattern) (ha : d2979 p = 1) (hb : d55841 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2974 q = 1) (hb : d55836 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d2974, d55836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro805 q ha hb
    | true =>
      simp only [d2974, d55836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2975 q = 1) (hb : d55837 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d2975, d55837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2975, d55837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2976 q = 1) (hb : d55838 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d2976, d55838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2976, d55838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2977 q = 1) (hb : d55839 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d2977, d55839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2977, d55839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2978 q = 1) (hb : d55840 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d2978, d55840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2978, d55840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2979 q = 1) (hb : d55841 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d2979, d55841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2979, d55841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro807 (p : Pattern) (ha : d2985 p = 1) (hb : d55847 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2980 q = 1) (hb : d55842 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d2980, d55842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro806 q ha hb
    | true =>
      simp only [d2980, d55842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2981 q = 1) (hb : d55843 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d2981, d55843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2981, d55843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2982 q = 1) (hb : d55844 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d2982, d55844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2982, d55844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2983 q = 1) (hb : d55845 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d2983, d55845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2983, d55845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2984 q = 1) (hb : d55846 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d2984, d55846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2984, d55846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2985 q = 1) (hb : d55847 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d2985, d55847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2985, d55847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro808 (p : Pattern) (ha : d2991 p = 1) (hb : d55853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2986 q = 1) (hb : d55848 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d2986, d55848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro807 q ha hb
    | true =>
      simp only [d2986, d55848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2987 q = 1) (hb : d55849 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d2987, d55849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2987, d55849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2988 q = 1) (hb : d55850 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d2988, d55850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2988, d55850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2989 q = 1) (hb : d55851 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d2989, d55851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2989, d55851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2990 q = 1) (hb : d55852 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d2990, d55852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2990, d55852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2991 q = 1) (hb : d55853 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d2991, d55853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2991, d55853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro809 (p : Pattern) (ha : d2997 p = 1) (hb : d55859 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2992 q = 1) (hb : d55854 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d2992, d55854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro808 q ha hb
    | true =>
      simp only [d2992, d55854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2993 q = 1) (hb : d55855 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d2993, d55855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2993, d55855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2994 q = 1) (hb : d55856 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d2994, d55856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2994, d55856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2995 q = 1) (hb : d55857 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d2995, d55857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2995, d55857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2996 q = 1) (hb : d55858 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d2996, d55858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2996, d55858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2997 q = 1) (hb : d55859 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d2997, d55859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2997, d55859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro810 (p : Pattern) (ha : d3003 p = 1) (hb : d55865 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2998 q = 1) (hb : d55860 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d2998, d55860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro809 q ha hb
    | true =>
      simp only [d2998, d55860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2999 q = 1) (hb : d55861 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d2999, d55861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2999, d55861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3000 q = 1) (hb : d55862 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d3000, d55862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3000, d55862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3001 q = 1) (hb : d55863 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d3001, d55863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3001, d55863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3002 q = 1) (hb : d55864 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d3002, d55864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3002, d55864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3003 q = 1) (hb : d55865 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d3003, d55865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3003, d55865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro811 (p : Pattern) (ha : d3009 p = 1) (hb : d55871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3004 q = 1) (hb : d55866 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d3004, d55866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro810 q ha hb
    | true =>
      simp only [d3004, d55866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3005 q = 1) (hb : d55867 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d3005, d55867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3005, d55867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3006 q = 1) (hb : d55868 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d3006, d55868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3006, d55868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3007 q = 1) (hb : d55869 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d3007, d55869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3007, d55869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3008 q = 1) (hb : d55870 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d3008, d55870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3008, d55870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3009 q = 1) (hb : d55871 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d3009, d55871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3009, d55871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro812 (p : Pattern) (ha : d3015 p = 1) (hb : d55877 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3010 q = 1) (hb : d55872 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d3010, d55872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro811 q ha hb
    | true =>
      simp only [d3010, d55872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3011 q = 1) (hb : d55873 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d3011, d55873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3011, d55873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3012 q = 1) (hb : d55874 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d3012, d55874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3012, d55874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3013 q = 1) (hb : d55875 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d3013, d55875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3013, d55875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3014 q = 1) (hb : d55876 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d3014, d55876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3014, d55876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3015 q = 1) (hb : d55877 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d3015, d55877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3015, d55877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro813 (p : Pattern) (ha : d54865 p = 1) (hb : d55754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53637 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53638 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, d55754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, d55754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54864 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54865 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro814 (p : Pattern) (ha : d54872 p = 1) (hb : d55754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53653 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53654 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, d55754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, d55754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54871 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54872 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro815 (p : Pattern) (ha : d54878 p = 1) (hb : d55754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54866 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro813 q ha hb
  have h2 (q : Pattern) (ha : d54867 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54868 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54869 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54870 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54873 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro814 q ha hb
  have h7 (q : Pattern) (ha : d54874 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54875 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54876 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54877 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54878 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro816 (p : Pattern) (ha : d54880 p = 1) (hb : d55754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53678 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53679 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53679, d55754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53679, d55754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54879 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54880 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro817 (p : Pattern) (ha : d54886 p = 1) (hb : d55754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54881 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro816 q ha hb
  have h2 (q : Pattern) (ha : d54882 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54883 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54884 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54885 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54886 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro818 (p : Pattern) (ha : d54889 p = 1) (hb : d55754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53705 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53706 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53706, d55754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53706, d55754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54888 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54889 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro819 (p : Pattern) (ha : d54895 p = 1) (hb : d55754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54890 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro818 q ha hb
  have h2 (q : Pattern) (ha : d54891 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54892 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54893 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54894 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54895 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro820 (p : Pattern) (ha : d54899 p = 1) (hb : d55754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53733 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53734 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53734, d55754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53734, d55754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54898 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54899 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro821 (p : Pattern) (ha : d54905 p = 1) (hb : d55754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54900 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro820 q ha hb
  have h2 (q : Pattern) (ha : d54901 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54902 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54903 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54904 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54905 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro822 (p : Pattern) (ha : d54910 p = 1) (hb : d55754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53762 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53763 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53763, d55754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53763, d55754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54909 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54910 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro823 (p : Pattern) (ha : d54916 p = 1) (hb : d55754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54911 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro822 q ha hb
  have h2 (q : Pattern) (ha : d54912 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54913 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54914 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54915 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54916 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro824 (p : Pattern) (ha : d54922 p = 1) (hb : d55754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53792 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53793 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53793, d55754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53793, d55754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54921 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54922 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro825 (p : Pattern) (ha : d54928 p = 1) (hb : d55754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54923 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro824 q ha hb
  have h2 (q : Pattern) (ha : d54924 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54925 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54926 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54927 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54928 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro826 (p : Pattern) (ha : d54934 p = 1) (hb : d55754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d54887 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro815 q ha hb
    | true =>
      simp only [d54887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro817 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54896 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro819 q ha hb
  have h3 (q : Pattern) (ha : d54897 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54906 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro821 q ha hb
  have h5 (q : Pattern) (ha : d54907 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54908 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54917 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro823 q ha hb
  have h8 (q : Pattern) (ha : d54918 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54919 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54920 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54929 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro825 q ha hb
  have h12 (q : Pattern) (ha : d54930 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54931 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54932 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54933 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54934 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d54934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro827 (p : Pattern) (ha : d54940 p = 1) (hb : d55754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54935 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro826 q ha hb
    | true =>
      simp only [d54935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54936 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54937 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54938 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54939 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54940 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d54940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro828 (p : Pattern) (ha : d54946 p = 1) (hb : d55754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54941 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro827 q ha hb
    | true =>
      simp only [d54941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54942 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54943 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54944 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54945 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54946 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d54946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro829 (p : Pattern) (ha : d54952 p = 1) (hb : d55754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54947 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro828 q ha hb
    | true =>
      simp only [d54947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54948 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54949 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54950 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54951 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54952 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d54952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro830 (p : Pattern) (ha : d54958 p = 1) (hb : d55754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54953 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro829 q ha hb
    | true =>
      simp only [d54953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54954 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54955 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54956 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54957 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54958 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d54958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro831 (p : Pattern) (ha : d54964 p = 1) (hb : d55754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54959 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro830 q ha hb
    | true =>
      simp only [d54959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54960 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54961 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54962 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54963 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54964 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d54964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro832 (p : Pattern) (ha : d54970 p = 1) (hb : d55754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54965 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro831 q ha hb
    | true =>
      simp only [d54965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54966 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54967 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54968 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54969 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54970 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro833 (p : Pattern) (ha : d54976 p = 1) (hb : d55757 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54971 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro832 q ha hb
    | true =>
      simp only [d54971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54972 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54973 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d54974 q = 1) (hb : d55756 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54974, d55756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54974, d55756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d54975 q = 1) (hb : d55757 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54975, d55757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54975, d55757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d55757 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d54976 q = 1) (hb : d55757 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro834 (p : Pattern) (ha : d0 p = 1) (hb : d55877 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55877 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro835 (p : Pattern) (ha : d0 p = 1) (hb : d3015 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d3015 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro836 (p : Pattern) (ha : d54520 p = 1) (hb : d55878 p = 1) : d54752 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d51650 q = 1) : d51650 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2528 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54517 q = 1) (hb : d54519 q = 1) : d54751 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54517, d54519, d54751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54517, d54519, d54751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54520 q = 1) (hb : d55878 q = 1) : d54752 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54520, d55878, d54752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d54520, d55878, d54752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro837 (p : Pattern) (ha : d54527 p = 1) (hb : d55878 p = 1) : d54759 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d51667 q = 1) : d51667 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2540 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54517 q = 1) (hb : d54526 q = 1) : d54758 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54517, d54526, d54758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54517, d54526, d54758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54527 q = 1) (hb : d55878 q = 1) : d54759 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54527, d55878, d54759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d54527, d55878, d54759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro838 (p : Pattern) (ha : d54533 p = 1) (hb : d55878 p = 1) : d54765 p = 1 := by
  have h0 (q : Pattern) (ha : d2524 q = 1) (hb : d55878 q = 1) : d2524 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54521 q = 1) (hb : d55878 q = 1) : d54753 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54521, d54753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54521, d54753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro836 q ha hb
  have h3 (q : Pattern) (ha : d54522 q = 1) (hb : d55878 q = 1) : d54754 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54522, d54754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54522, d54754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54523 q = 1) (hb : d55878 q = 1) : d54755 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54523, d54755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54523, d54755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54524 q = 1) (hb : d55878 q = 1) : d54756 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54524, d54756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54524, d54756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54525 q = 1) (hb : d55878 q = 1) : d54757 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54525, d54757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54525, d54757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54528 q = 1) (hb : d55878 q = 1) : d54760 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54528, d54760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54528, d54760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro837 q ha hb
  have h8 (q : Pattern) (ha : d54529 q = 1) (hb : d55878 q = 1) : d54761 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54529, d54761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54529, d54761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54530 q = 1) (hb : d55878 q = 1) : d54762 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54530, d54762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54530, d54762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54531 q = 1) (hb : d55878 q = 1) : d54763 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54531, d54763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54531, d54763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54532 q = 1) (hb : d55878 q = 1) : d54764 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54532, d54764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54532, d54764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54533 q = 1) (hb : d55878 q = 1) : d54765 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54533, d54765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54533, d54765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro839 (p : Pattern) (ha : d54535 p = 1) (hb : d55878 p = 1) : d54767 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d51692 q = 1) : d51692 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2553 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54517 q = 1) (hb : d54534 q = 1) : d54766 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54517, d54534, d54766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54517, d54534, d54766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54535 q = 1) (hb : d55878 q = 1) : d54767 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54535, d55878, d54767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d54535, d55878, d54767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro840 (p : Pattern) (ha : d54541 p = 1) (hb : d55878 p = 1) : d54773 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54536 q = 1) (hb : d55878 q = 1) : d54768 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54536, d54768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54536, d54768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro839 q ha hb
  have h2 (q : Pattern) (ha : d54537 q = 1) (hb : d55878 q = 1) : d54769 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54537, d54769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54537, d54769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54538 q = 1) (hb : d55878 q = 1) : d54770 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54538, d54770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54538, d54770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54539 q = 1) (hb : d55878 q = 1) : d54771 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54539, d54771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54539, d54771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54540 q = 1) (hb : d55878 q = 1) : d54772 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54540, d54772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54540, d54772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54541 q = 1) (hb : d55878 q = 1) : d54773 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54541, d54773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54541, d54773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro841 (p : Pattern) (ha : d54544 p = 1) (hb : d55878 p = 1) : d54776 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d51718 q = 1) : d51718 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2567 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54517 q = 1) (hb : d54543 q = 1) : d54775 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54517, d54543, d54775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54517, d54543, d54775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54544 q = 1) (hb : d55878 q = 1) : d54776 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54544, d55878, d54776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d54544, d55878, d54776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro842 (p : Pattern) (ha : d54550 p = 1) (hb : d55878 p = 1) : d54782 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54545 q = 1) (hb : d55878 q = 1) : d54777 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54545, d54777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54545, d54777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro841 q ha hb
  have h2 (q : Pattern) (ha : d54546 q = 1) (hb : d55878 q = 1) : d54778 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54546, d54778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54546, d54778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54547 q = 1) (hb : d55878 q = 1) : d54779 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54547, d54779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54547, d54779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54548 q = 1) (hb : d55878 q = 1) : d54780 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54548, d54780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54548, d54780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54549 q = 1) (hb : d55878 q = 1) : d54781 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54549, d54781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54549, d54781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54550 q = 1) (hb : d55878 q = 1) : d54782 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54550, d54782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54550, d54782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro843 (p : Pattern) (ha : d54554 p = 1) (hb : d55878 p = 1) : d54786 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d51745 q = 1) : d51745 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2582 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54517 q = 1) (hb : d54553 q = 1) : d54785 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54517, d54553, d54785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54517, d54553, d54785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54554 q = 1) (hb : d55878 q = 1) : d54786 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54554, d55878, d54786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d54554, d55878, d54786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro844 (p : Pattern) (ha : d54560 p = 1) (hb : d55878 p = 1) : d54792 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54555 q = 1) (hb : d55878 q = 1) : d54787 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54555, d54787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54555, d54787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro843 q ha hb
  have h2 (q : Pattern) (ha : d54556 q = 1) (hb : d55878 q = 1) : d54788 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54556, d54788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54556, d54788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54557 q = 1) (hb : d55878 q = 1) : d54789 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54557, d54789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54557, d54789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54558 q = 1) (hb : d55878 q = 1) : d54790 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54558, d54790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54558, d54790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54559 q = 1) (hb : d55878 q = 1) : d54791 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54559, d54791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54559, d54791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54560 q = 1) (hb : d55878 q = 1) : d54792 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54560, d54792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54560, d54792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro845 (p : Pattern) (ha : d54565 p = 1) (hb : d55878 p = 1) : d54797 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d51773 q = 1) : d51773 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2598 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54517 q = 1) (hb : d54564 q = 1) : d54796 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54517, d54564, d54796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54517, d54564, d54796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54565 q = 1) (hb : d55878 q = 1) : d54797 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54565, d55878, d54797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d54565, d55878, d54797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro846 (p : Pattern) (ha : d54571 p = 1) (hb : d55878 p = 1) : d54803 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54566 q = 1) (hb : d55878 q = 1) : d54798 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54566, d54798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54566, d54798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro845 q ha hb
  have h2 (q : Pattern) (ha : d54567 q = 1) (hb : d55878 q = 1) : d54799 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54567, d54799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54567, d54799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54568 q = 1) (hb : d55878 q = 1) : d54800 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54568, d54800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54568, d54800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54569 q = 1) (hb : d55878 q = 1) : d54801 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54569, d54801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54569, d54801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54570 q = 1) (hb : d55878 q = 1) : d54802 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54570, d54802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54570, d54802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54571 q = 1) (hb : d55878 q = 1) : d54803 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54571, d54803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54571, d54803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro847 (p : Pattern) (ha : d54577 p = 1) (hb : d55878 p = 1) : d54809 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d51802 q = 1) : d51802 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2615 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54517 q = 1) (hb : d54576 q = 1) : d54808 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54517, d54576, d54808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54517, d54576, d54808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54577 q = 1) (hb : d55878 q = 1) : d54809 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54577, d55878, d54809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d54577, d55878, d54809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro848 (p : Pattern) (ha : d54583 p = 1) (hb : d55878 p = 1) : d54815 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54578 q = 1) (hb : d55878 q = 1) : d54810 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54578, d54810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54578, d54810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro847 q ha hb
  have h2 (q : Pattern) (ha : d54579 q = 1) (hb : d55878 q = 1) : d54811 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54579, d54811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54579, d54811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54580 q = 1) (hb : d55878 q = 1) : d54812 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54580, d54812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54580, d54812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54581 q = 1) (hb : d55878 q = 1) : d54813 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54581, d54813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54581, d54813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54582 q = 1) (hb : d55878 q = 1) : d54814 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54582, d54814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54582, d54814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54583 q = 1) (hb : d55878 q = 1) : d54815 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54583, d54815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54583, d54815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro849 (p : Pattern) (ha : d54589 p = 1) (hb : d55878 p = 1) : d54821 p = 1 := by
  have h0 (q : Pattern) (ha : d54542 q = 1) (hb : d55878 q = 1) : d54774 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54542, d54774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro838 q ha hb
    | true =>
      simp only [d54542, d54774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro840 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54551 q = 1) (hb : d55878 q = 1) : d54783 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54551, d54783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54551, d54783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro842 q ha hb
  have h3 (q : Pattern) (ha : d54552 q = 1) (hb : d55878 q = 1) : d54784 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54552, d54784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54552, d54784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54561 q = 1) (hb : d55878 q = 1) : d54793 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54561, d54793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54561, d54793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro844 q ha hb
  have h5 (q : Pattern) (ha : d54562 q = 1) (hb : d55878 q = 1) : d54794 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54562, d54794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54562, d54794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54563 q = 1) (hb : d55878 q = 1) : d54795 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54563, d54795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54563, d54795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54572 q = 1) (hb : d55878 q = 1) : d54804 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54572, d54804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54572, d54804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro846 q ha hb
  have h8 (q : Pattern) (ha : d54573 q = 1) (hb : d55878 q = 1) : d54805 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54573, d54805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54573, d54805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54574 q = 1) (hb : d55878 q = 1) : d54806 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54574, d54806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54574, d54806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54575 q = 1) (hb : d55878 q = 1) : d54807 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54575, d54807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54575, d54807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54584 q = 1) (hb : d55878 q = 1) : d54816 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54584, d54816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54584, d54816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro848 q ha hb
  have h12 (q : Pattern) (ha : d54585 q = 1) (hb : d55878 q = 1) : d54817 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54585, d54817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54585, d54817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54586 q = 1) (hb : d55878 q = 1) : d54818 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54586, d54818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54586, d54818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54587 q = 1) (hb : d55878 q = 1) : d54819 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54587, d54819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54587, d54819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54588 q = 1) (hb : d55878 q = 1) : d54820 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54588, d54820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54588, d54820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54589 q = 1) (hb : d55878 q = 1) : d54821 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d54589, d54821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54589, d54821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro850 (p : Pattern) (ha : d54595 p = 1) (hb : d55878 p = 1) : d54827 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54590 q = 1) (hb : d55878 q = 1) : d54822 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54590, d54822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro849 q ha hb
    | true =>
      simp only [d54590, d54822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54591 q = 1) (hb : d55878 q = 1) : d54823 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54591, d54823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54591, d54823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54592 q = 1) (hb : d55878 q = 1) : d54824 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54592, d54824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54592, d54824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54593 q = 1) (hb : d55878 q = 1) : d54825 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54593, d54825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54593, d54825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54594 q = 1) (hb : d55878 q = 1) : d54826 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54594, d54826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54594, d54826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54595 q = 1) (hb : d55878 q = 1) : d54827 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d54595, d54827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54595, d54827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro851 (p : Pattern) (ha : d54601 p = 1) (hb : d55878 p = 1) : d54833 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54596 q = 1) (hb : d55878 q = 1) : d54828 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54596, d54828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro850 q ha hb
    | true =>
      simp only [d54596, d54828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54597 q = 1) (hb : d55878 q = 1) : d54829 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54597, d54829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54597, d54829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54598 q = 1) (hb : d55878 q = 1) : d54830 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54598, d54830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54598, d54830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54599 q = 1) (hb : d55878 q = 1) : d54831 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54599, d54831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54599, d54831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54600 q = 1) (hb : d55878 q = 1) : d54832 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54600, d54832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54600, d54832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54601 q = 1) (hb : d55878 q = 1) : d54833 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d54601, d54833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54601, d54833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro852 (p : Pattern) (ha : d54607 p = 1) (hb : d55878 p = 1) : d54839 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54602 q = 1) (hb : d55878 q = 1) : d54834 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54602, d54834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro851 q ha hb
    | true =>
      simp only [d54602, d54834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54603 q = 1) (hb : d55878 q = 1) : d54835 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54603, d54835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54603, d54835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54604 q = 1) (hb : d55878 q = 1) : d54836 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54604, d54836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54604, d54836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54605 q = 1) (hb : d55878 q = 1) : d54837 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54605, d54837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54605, d54837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54606 q = 1) (hb : d55878 q = 1) : d54838 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54606, d54838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54606, d54838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54607 q = 1) (hb : d55878 q = 1) : d54839 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d54607, d54839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54607, d54839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro853 (p : Pattern) (ha : d54613 p = 1) (hb : d55878 p = 1) : d54845 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54608 q = 1) (hb : d55878 q = 1) : d54840 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54608, d54840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro852 q ha hb
    | true =>
      simp only [d54608, d54840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54609 q = 1) (hb : d55878 q = 1) : d54841 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54609, d54841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54609, d54841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54610 q = 1) (hb : d55878 q = 1) : d54842 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54610, d54842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54610, d54842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54611 q = 1) (hb : d55878 q = 1) : d54843 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54611, d54843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54611, d54843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54612 q = 1) (hb : d55878 q = 1) : d54844 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54612, d54844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54612, d54844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54613 q = 1) (hb : d55878 q = 1) : d54845 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d54613, d54845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54613, d54845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro854 (p : Pattern) (ha : d54619 p = 1) (hb : d55878 p = 1) : d54851 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54614 q = 1) (hb : d55878 q = 1) : d54846 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54614, d54846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro853 q ha hb
    | true =>
      simp only [d54614, d54846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54615 q = 1) (hb : d55878 q = 1) : d54847 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54615, d54847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54615, d54847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54616 q = 1) (hb : d55878 q = 1) : d54848 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54616, d54848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54616, d54848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54617 q = 1) (hb : d55878 q = 1) : d54849 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54617, d54849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54617, d54849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54618 q = 1) (hb : d55878 q = 1) : d54850 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54618, d54850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54618, d54850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54619 q = 1) (hb : d55878 q = 1) : d54851 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d54619, d54851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54619, d54851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro855 (p : Pattern) (ha : d54625 p = 1) (hb : d55878 p = 1) : d54857 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54620 q = 1) (hb : d55878 q = 1) : d54852 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54620, d54852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro854 q ha hb
    | true =>
      simp only [d54620, d54852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54621 q = 1) (hb : d55878 q = 1) : d54853 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54621, d54853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54621, d54853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54622 q = 1) (hb : d55878 q = 1) : d54854 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54622, d54854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54622, d54854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54623 q = 1) (hb : d55878 q = 1) : d54855 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54623, d54855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54623, d54855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54624 q = 1) (hb : d55878 q = 1) : d54856 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54624, d54856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54624, d54856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54625 q = 1) (hb : d55878 q = 1) : d54857 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54625, d54857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54625, d54857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro856 (p : Pattern) (ha : d54631 p = 1) (hb : d55879 p = 1) : d54863 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54626 q = 1) (hb : d55878 q = 1) : d54858 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54626, d54858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro855 q ha hb
    | true =>
      simp only [d54626, d54858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54627 q = 1) (hb : d55878 q = 1) : d54859 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54627, d54859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54627, d54859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54628 q = 1) (hb : d55878 q = 1) : d54860 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54628, d54860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54628, d54860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54629 q = 1) (hb : d55878 q = 1) : d54861 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54629, d54861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54629, d54861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54630 q = 1) (hb : d55879 q = 1) : d54862 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54630, d55879, d54862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54630, d55879, d54862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d55879 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54631 q = 1) (hb : d55879 q = 1) : d54863 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54631, d54863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54631, d54863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro857 (p : Pattern) (ha : d2520 p = 1) (hb : d54187 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56 q = 1) (hb : d51908 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56, d51908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6 q ha hb
    | true =>
      simp only [d56, d51908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8 q ha hb
  have h2 (q : Pattern) (ha : d57 q = 1) (hb : d51909 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57, d51909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57, d51909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58 q = 1) (hb : d51910 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58, d51910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58, d51910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d59 q = 1) (hb : d51911 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59, d51911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59, d51911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d51916 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2519 q = 1) (hb : d51917 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2519, d51917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2519, d51917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2520 q = 1) (hb : d54187 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2520, d54187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2520, d54187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro858 (p : Pattern) (ha : d54192 p = 1) (hb : d54752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d51957 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, d51957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, d51957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d51958 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, d51958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, d51958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d51964 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d51964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15 q ha hb
    | true =>
      simp only [d112, d51964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d51965 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d51965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, d51965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, d51966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, d51966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51647 q = 1) (hb : d52030 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51647, d52030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31 q ha hb
    | true =>
      simp only [d51647, d52030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17 q ha hb
    | true =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d51648 q = 1) (hb : d52033 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51648, d52033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51648, d52033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51649 q = 1) (hb : d52034 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51649, d52034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51649, d52034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51650 q = 1) (hb : d52035 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51650, d52035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51650, d52035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52042 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d52043 q = 1) (hb : d54751 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52043, d54751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d52043, d54751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d54192 q = 1) (hb : d54752 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54192, d54752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54192, d54752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro859 (p : Pattern) (ha : d54198 p = 1) (hb : d54759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d52084 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, d52084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, d52084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36 q ha hb
  have h2 (q : Pattern) (ha : d286 q = 1) (hb : d52085 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, d52085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, d52085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d292 q = 1) (hb : d52091 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d52091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36 q ha hb
    | true =>
      simp only [d292, d52091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37 q ha hb
  have h4 (q : Pattern) (ha : d293 q = 1) (hb : d52092 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d52092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293, d52092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d294 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, d52093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d294, d52093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51664 q = 1) (hb : d52162 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51664, d52162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54 q ha hb
    | true =>
      simp only [d51664, d52162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57 q ha hb
  have h7 (q : Pattern) (ha : d398 q = 1) (hb : d52164 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d398, d52164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38 q ha hb
    | true =>
      simp only [d398, d52164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q ha hb
  have h8 (q : Pattern) (ha : d51665 q = 1) (hb : d52165 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51665, d52165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51665, d52165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51666 q = 1) (hb : d52166 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51666, d52166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51666, d52166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51667 q = 1) (hb : d52167 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51667, d52167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51667, d52167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52176 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d52177 q = 1) (hb : d54758 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52177, d54758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d52177, d54758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d54198 q = 1) (hb : d54759 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54198, d54759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54198, d54759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro860 (p : Pattern) (ha : d54204 p = 1) (hb : d54765 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2521 q = 1) (hb : d54188 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2521, d54188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2521, d54188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro857 q ha hb
  have h2 (q : Pattern) (ha : d2522 q = 1) (hb : d54189 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2522, d54189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2522, d54189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2523 q = 1) (hb : d54190 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2523, d54190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2523, d54190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2524 q = 1) (hb : d54191 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2524, d54191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2524, d54191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54193 q = 1) (hb : d54753 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54193, d54753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54193, d54753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro858 q ha hb
  have h6 (q : Pattern) (ha : d54194 q = 1) (hb : d54754 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54194, d54754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54194, d54754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54195 q = 1) (hb : d54755 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54195, d54755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54195, d54755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54196 q = 1) (hb : d54756 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54196, d54756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54196, d54756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54197 q = 1) (hb : d54757 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54197, d54757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d54197, d54757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54199 q = 1) (hb : d54760 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54199, d54760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54199, d54760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro859 q ha hb
  have h11 (q : Pattern) (ha : d54200 q = 1) (hb : d54761 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54200, d54761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54200, d54761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54201 q = 1) (hb : d54762 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54201, d54762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54201, d54762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54202 q = 1) (hb : d54763 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54202, d54763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54202, d54763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54203 q = 1) (hb : d54764 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54203, d54764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54203, d54764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54204 q = 1) (hb : d54765 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54204, d54765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d54204, d54765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro861 (p : Pattern) (ha : d54205 p = 1) (hb : d54767 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d498 q = 1) (hb : d52245 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d498, d52245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d498, d52245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64 q ha hb
  have h2 (q : Pattern) (ha : d499 q = 1) (hb : d52246 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d499, d52246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d499, d52246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d508 q = 1) (hb : d52255 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d52255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64 q ha hb
    | true =>
      simp only [d508, d52255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67 q ha hb
  have h4 (q : Pattern) (ha : d509 q = 1) (hb : d52256 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d52256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d509, d52256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d510 q = 1) (hb : d52257 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d510, d52257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d510, d52257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51689 q = 1) (hb : d52336 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51689, d52336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92 q ha hb
    | true =>
      simp only [d51689, d52336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97 q ha hb
  have h7 (q : Pattern) (ha : d645 q = 1) (hb : d52349 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d645, d52349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68 q ha hb
    | true =>
      simp only [d645, d52349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69 q ha hb
  have h8 (q : Pattern) (ha : d51690 q = 1) (hb : d52350 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51690, d52350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51690, d52350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51691 q = 1) (hb : d52351 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51691, d52351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51691, d52351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51692 q = 1) (hb : d52352 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51692, d52352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51692, d52352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52361 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d52362 q = 1) (hb : d54766 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52362, d54766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d52362, d54766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d54205 q = 1) (hb : d54767 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54205, d54767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54205, d54767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro862 (p : Pattern) (ha : d54211 p = 1) (hb : d54773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54206 q = 1) (hb : d54768 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54206, d54768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54206, d54768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro861 q ha hb
  have h2 (q : Pattern) (ha : d54207 q = 1) (hb : d54769 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54207, d54769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54207, d54769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54208 q = 1) (hb : d54770 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54208, d54770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54208, d54770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54209 q = 1) (hb : d54771 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54209, d54771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54209, d54771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54210 q = 1) (hb : d54772 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54210, d54772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54210, d54772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54211 q = 1) (hb : d54773 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54211, d54773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54211, d54773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro863 (p : Pattern) (ha : d54213 p = 1) (hb : d54776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d790 q = 1) (hb : d52467 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d790, d52467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d790, d52467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108 q ha hb
  have h2 (q : Pattern) (ha : d791 q = 1) (hb : d52468 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d791, d52468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d791, d52468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d800 q = 1) (hb : d52477 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d52477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108 q ha hb
    | true =>
      simp only [d800, d52477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro111 q ha hb
  have h4 (q : Pattern) (ha : d801 q = 1) (hb : d52478 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d52478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d801, d52478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d802 q = 1) (hb : d52479 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d802, d52479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d802, d52479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51715 q = 1) (hb : d52557 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51715, d52557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro139 q ha hb
    | true =>
      simp only [d51715, d52557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro144 q ha hb
  have h7 (q : Pattern) (ha : d951 q = 1) (hb : d52570 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d951, d52570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro112 q ha hb
    | true =>
      simp only [d951, d52570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro113 q ha hb
  have h8 (q : Pattern) (ha : d51716 q = 1) (hb : d52571 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51716, d52571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51716, d52571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51717 q = 1) (hb : d52572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51717, d52572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51717, d52572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51718 q = 1) (hb : d52573 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51718, d52573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51718, d52573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52582 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d52583 q = 1) (hb : d54775 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52583, d54775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d52583, d54775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d54213 q = 1) (hb : d54776 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54213, d54776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54213, d54776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro864 (p : Pattern) (ha : d54219 p = 1) (hb : d54782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54214 q = 1) (hb : d54777 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54214, d54777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54214, d54777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro863 q ha hb
  have h2 (q : Pattern) (ha : d54215 q = 1) (hb : d54778 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54215, d54778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54215, d54778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54216 q = 1) (hb : d54779 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54216, d54779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54216, d54779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54217 q = 1) (hb : d54780 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54217, d54780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54217, d54780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54218 q = 1) (hb : d54781 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54218, d54781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54218, d54781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54219 q = 1) (hb : d54782 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54219, d54782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54219, d54782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro865 (p : Pattern) (ha : d54222 p = 1) (hb : d54786 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1169 q = 1) (hb : d52750 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1169, d52750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1169, d52750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro160 q ha hb
  have h2 (q : Pattern) (ha : d1170 q = 1) (hb : d52751 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1170, d52751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1170, d52751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1179 q = 1) (hb : d52760 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d52760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro160 q ha hb
    | true =>
      simp only [d1179, d52760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro163 q ha hb
  have h4 (q : Pattern) (ha : d1180 q = 1) (hb : d52761 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d52761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1180, d52761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1181 q = 1) (hb : d52762 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1181, d52762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1181, d52762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51742 q = 1) (hb : d52837 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51742, d52837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro191 q ha hb
    | true =>
      simp only [d51742, d52837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro196 q ha hb
  have h7 (q : Pattern) (ha : d1362 q = 1) (hb : d52850 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1362, d52850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro164 q ha hb
    | true =>
      simp only [d1362, d52850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro165 q ha hb
  have h8 (q : Pattern) (ha : d51743 q = 1) (hb : d52851 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51743, d52851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51743, d52851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51744 q = 1) (hb : d52852 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51744, d52852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51744, d52852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51745 q = 1) (hb : d52853 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51745, d52853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51745, d52853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52862 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d52863 q = 1) (hb : d54785 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52863, d54785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d52863, d54785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d54222 q = 1) (hb : d54786 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54222, d54786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54222, d54786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro866 (p : Pattern) (ha : d54228 p = 1) (hb : d54792 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54223 q = 1) (hb : d54787 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54223, d54787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54223, d54787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro865 q ha hb
  have h2 (q : Pattern) (ha : d54224 q = 1) (hb : d54788 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54224, d54788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54224, d54788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54225 q = 1) (hb : d54789 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54225, d54789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54225, d54789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54226 q = 1) (hb : d54790 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54226, d54790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54226, d54790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54227 q = 1) (hb : d54791 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54227, d54791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54227, d54791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54228 q = 1) (hb : d54792 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54228, d54792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54228, d54792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro867 (p : Pattern) (ha : d54232 p = 1) (hb : d54797 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1630 q = 1) (hb : d53071 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1630, d53071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1630, d53071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro218 q ha hb
  have h2 (q : Pattern) (ha : d1631 q = 1) (hb : d53072 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1631, d53072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1631, d53072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1640 q = 1) (hb : d53081 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d53081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro218 q ha hb
    | true =>
      simp only [d1640, d53081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro221 q ha hb
  have h4 (q : Pattern) (ha : d1641 q = 1) (hb : d53082 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d53082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1641, d53082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1642 q = 1) (hb : d53083 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1642, d53083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1642, d53083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51770 q = 1) (hb : d53152 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51770, d53152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro247 q ha hb
    | true =>
      simp only [d51770, d53152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro252 q ha hb
  have h7 (q : Pattern) (ha : d1839 q = 1) (hb : d53165 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1839, d53165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro222 q ha hb
    | true =>
      simp only [d1839, d53165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro223 q ha hb
  have h8 (q : Pattern) (ha : d51771 q = 1) (hb : d53166 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51771, d53166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51771, d53166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51772 q = 1) (hb : d53167 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51772, d53167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51772, d53167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51773 q = 1) (hb : d53168 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51773, d53168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51773, d53168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d53177 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d53178 q = 1) (hb : d54796 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53178, d54796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d53178, d54796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d54232 q = 1) (hb : d54797 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54232, d54797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54232, d54797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro868 (p : Pattern) (ha : d54238 p = 1) (hb : d54803 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54233 q = 1) (hb : d54798 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54233, d54798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54233, d54798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro867 q ha hb
  have h2 (q : Pattern) (ha : d54234 q = 1) (hb : d54799 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54234, d54799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54234, d54799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54235 q = 1) (hb : d54800 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54235, d54800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54235, d54800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54236 q = 1) (hb : d54801 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54236, d54801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54236, d54801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54237 q = 1) (hb : d54802 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54237, d54802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54237, d54802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54238 q = 1) (hb : d54803 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54238, d54803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54238, d54803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro869 (p : Pattern) (ha : d54243 p = 1) (hb : d54809 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2113 q = 1) (hb : d53392 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2113, d53392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2113, d53392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro277 q ha hb
  have h2 (q : Pattern) (ha : d2114 q = 1) (hb : d53393 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2114, d53393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2114, d53393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2123 q = 1) (hb : d53402 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d53402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro277 q ha hb
    | true =>
      simp only [d2123, d53402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro280 q ha hb
  have h4 (q : Pattern) (ha : d2124 q = 1) (hb : d53403 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d53403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2124, d53403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2125 q = 1) (hb : d53404 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2125, d53404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2125, d53404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51799 q = 1) (hb : d53469 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51799, d53469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro306 q ha hb
    | true =>
      simp only [d51799, d53469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro311 q ha hb
  have h7 (q : Pattern) (ha : d2317 q = 1) (hb : d53482 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2317, d53482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro281 q ha hb
    | true =>
      simp only [d2317, d53482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro282 q ha hb
  have h8 (q : Pattern) (ha : d51800 q = 1) (hb : d53483 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51800, d53483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51800, d53483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51801 q = 1) (hb : d53484 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51801, d53484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51801, d53484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51802 q = 1) (hb : d53485 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51802, d53485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51802, d53485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d53494 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d53495 q = 1) (hb : d54808 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53495, d54808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d53495, d54808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d54243 q = 1) (hb : d54809 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54243, d54809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54243, d54809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro870 (p : Pattern) (ha : d54249 p = 1) (hb : d54815 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54244 q = 1) (hb : d54810 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54244, d54810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54244, d54810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro869 q ha hb
  have h2 (q : Pattern) (ha : d54245 q = 1) (hb : d54811 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54245, d54811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54245, d54811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54246 q = 1) (hb : d54812 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54246, d54812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54246, d54812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54247 q = 1) (hb : d54813 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54247, d54813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54247, d54813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54248 q = 1) (hb : d54814 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54248, d54814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54248, d54814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54249 q = 1) (hb : d54815 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54249, d54815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54249, d54815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro871 (p : Pattern) (ha : d54255 p = 1) (hb : d54821 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d54212 q = 1) (hb : d54774 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54212, d54774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro860 q ha hb
    | true =>
      simp only [d54212, d54774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro862 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54220 q = 1) (hb : d54783 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54220, d54783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54220, d54783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro864 q ha hb
  have h3 (q : Pattern) (ha : d54221 q = 1) (hb : d54784 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54221, d54784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54221, d54784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54229 q = 1) (hb : d54793 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54229, d54793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54229, d54793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro866 q ha hb
  have h5 (q : Pattern) (ha : d54230 q = 1) (hb : d54794 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54230, d54794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54230, d54794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54231 q = 1) (hb : d54795 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54231, d54795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54231, d54795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54239 q = 1) (hb : d54804 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54239, d54804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54239, d54804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro868 q ha hb
  have h8 (q : Pattern) (ha : d54240 q = 1) (hb : d54805 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54240, d54805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54240, d54805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54241 q = 1) (hb : d54806 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54241, d54806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54241, d54806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54242 q = 1) (hb : d54807 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54242, d54807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54242, d54807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54250 q = 1) (hb : d54816 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54250, d54816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54250, d54816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro870 q ha hb
  have h12 (q : Pattern) (ha : d54251 q = 1) (hb : d54817 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54251, d54817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54251, d54817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54252 q = 1) (hb : d54818 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54252, d54818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54252, d54818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54253 q = 1) (hb : d54819 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54253, d54819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54253, d54819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54254 q = 1) (hb : d54820 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54254, d54820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54254, d54820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54255 q = 1) (hb : d54821 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d54255, d54821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54255, d54821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro872 (p : Pattern) (ha : d54261 p = 1) (hb : d54827 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54256 q = 1) (hb : d54822 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54256, d54822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro871 q ha hb
    | true =>
      simp only [d54256, d54822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54257 q = 1) (hb : d54823 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54257, d54823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54257, d54823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54258 q = 1) (hb : d54824 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54258, d54824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54258, d54824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54259 q = 1) (hb : d54825 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54259, d54825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54259, d54825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54260 q = 1) (hb : d54826 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54260, d54826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54260, d54826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54261 q = 1) (hb : d54827 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d54261, d54827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54261, d54827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro873 (p : Pattern) (ha : d54267 p = 1) (hb : d54833 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54262 q = 1) (hb : d54828 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54262, d54828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro872 q ha hb
    | true =>
      simp only [d54262, d54828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54263 q = 1) (hb : d54829 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54263, d54829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54263, d54829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54264 q = 1) (hb : d54830 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54264, d54830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54264, d54830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54265 q = 1) (hb : d54831 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54265, d54831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54265, d54831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54266 q = 1) (hb : d54832 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54266, d54832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54266, d54832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54267 q = 1) (hb : d54833 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d54267, d54833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54267, d54833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro874 (p : Pattern) (ha : d54273 p = 1) (hb : d54839 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54268 q = 1) (hb : d54834 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54268, d54834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro873 q ha hb
    | true =>
      simp only [d54268, d54834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54269 q = 1) (hb : d54835 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54269, d54835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54269, d54835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54270 q = 1) (hb : d54836 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54270, d54836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54270, d54836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54271 q = 1) (hb : d54837 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54271, d54837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54271, d54837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54272 q = 1) (hb : d54838 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54272, d54838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54272, d54838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54273 q = 1) (hb : d54839 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d54273, d54839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54273, d54839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro875 (p : Pattern) (ha : d54279 p = 1) (hb : d54845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54274 q = 1) (hb : d54840 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54274, d54840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro874 q ha hb
    | true =>
      simp only [d54274, d54840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54275 q = 1) (hb : d54841 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54275, d54841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54275, d54841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54276 q = 1) (hb : d54842 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54276, d54842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54276, d54842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54277 q = 1) (hb : d54843 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54277, d54843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54277, d54843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54278 q = 1) (hb : d54844 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54278, d54844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54278, d54844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54279 q = 1) (hb : d54845 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d54279, d54845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54279, d54845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro876 (p : Pattern) (ha : d54285 p = 1) (hb : d54851 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54280 q = 1) (hb : d54846 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54280, d54846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro875 q ha hb
    | true =>
      simp only [d54280, d54846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54281 q = 1) (hb : d54847 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54281, d54847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54281, d54847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54282 q = 1) (hb : d54848 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54282, d54848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54282, d54848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54283 q = 1) (hb : d54849 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54283, d54849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54283, d54849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54284 q = 1) (hb : d54850 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54284, d54850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54284, d54850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54285 q = 1) (hb : d54851 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d54285, d54851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54285, d54851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro877 (p : Pattern) (ha : d54291 p = 1) (hb : d54857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54286 q = 1) (hb : d54852 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54286, d54852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro876 q ha hb
    | true =>
      simp only [d54286, d54852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54287 q = 1) (hb : d54853 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54287, d54853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54287, d54853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54288 q = 1) (hb : d54854 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54288, d54854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54288, d54854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54289 q = 1) (hb : d54855 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54289, d54855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54289, d54855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54290 q = 1) (hb : d54856 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54290, d54856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54290, d54856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54291 q = 1) (hb : d54857 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54291, d54857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54291, d54857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro878 (p : Pattern) (ha : d54297 p = 1) (hb : d54863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54292 q = 1) (hb : d54858 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54292, d54858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro877 q ha hb
    | true =>
      simp only [d54292, d54858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54293 q = 1) (hb : d54859 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54293, d54859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54293, d54859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54294 q = 1) (hb : d54860 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54294, d54860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54294, d54860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54295 q = 1) (hb : d54861 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54295, d54861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54295, d54861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54296 q = 1) (hb : d54862 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54296, d54862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54296, d54862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54297 q = 1) (hb : d54863 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54297, d54863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54297, d54863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro879 (p : Pattern) (ha : d54976 p = 1) (hb : d55879 p = 1) : d54976 p = 1 := by
  have h0 (q : Pattern) (ha : d54976 q = 1) (hb : d55879 q = 1) : d54976 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro880 (p : Pattern) (ha : d54192 p = 1) (hb : d54865 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d52030 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d52030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro323 q ha hb
    | true =>
      simp only [d112, d52030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro324 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113 q = 1) (hb : d52033 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d52033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, d52033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52034 q = 1) (hb : d53637 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52034, d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d52034, d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52035 q = 1) (hb : d53638 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52035, d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52035, d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52042 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d52043 q = 1) (hb : d54864 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52043, d54864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52043, d54864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d54192 q = 1) (hb : d54865 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54192, d54865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54192, d54865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  exact h9 p ha hb
theorem andIntro881 (p : Pattern) (ha : d54198 p = 1) (hb : d54872 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292 q = 1) (hb : d52162 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d52162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro328 q ha hb
    | true =>
      simp only [d292, d52162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro329 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52164 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d293 q = 1) (hb : d52165 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d52165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293, d52165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52166 q = 1) (hb : d53653 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52166, d53653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d52166, d53653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52167 q = 1) (hb : d53654 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52167, d53654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52167, d53654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52176 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d52177 q = 1) (hb : d54871 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52177, d54871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52177, d54871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d54198 q = 1) (hb : d54872 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54198, d54872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54198, d54872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  exact h9 p ha hb
theorem andIntro882 (p : Pattern) (ha : d54204 p = 1) (hb : d54878 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54193 q = 1) (hb : d54866 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54193, d54866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54193, d54866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro880 q ha hb
  have h3 (q : Pattern) (ha : d54194 q = 1) (hb : d54867 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54194, d54867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54194, d54867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54195 q = 1) (hb : d54868 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54195, d54868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54195, d54868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54196 q = 1) (hb : d54869 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54196, d54869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54196, d54869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54197 q = 1) (hb : d54870 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54197, d54870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54197, d54870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54199 q = 1) (hb : d54873 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54199, d54873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54199, d54873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro881 q ha hb
  have h8 (q : Pattern) (ha : d54200 q = 1) (hb : d54874 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54200, d54874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54200, d54874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54201 q = 1) (hb : d54875 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54201, d54875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54201, d54875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54202 q = 1) (hb : d54876 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54202, d54876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54202, d54876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54203 q = 1) (hb : d54877 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54203, d54877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54203, d54877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54204 q = 1) (hb : d54878 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54204, d54878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54204, d54878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro883 (p : Pattern) (ha : d54205 p = 1) (hb : d54880 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52257 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d508 q = 1) (hb : d52336 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d52336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro334 q ha hb
    | true =>
      simp only [d508, d52336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro335 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52349 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d509 q = 1) (hb : d52350 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d52350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d509, d52350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52351 q = 1) (hb : d53678 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52351, d53678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d52351, d53678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52352 q = 1) (hb : d53679 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52352, d53679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52352, d53679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52361 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d52362 q = 1) (hb : d54879 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52362, d54879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52362, d54879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d54205 q = 1) (hb : d54880 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54205, d54880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54205, d54880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  exact h9 p ha hb
theorem andIntro884 (p : Pattern) (ha : d54211 p = 1) (hb : d54886 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54206 q = 1) (hb : d54881 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54206, d54881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54206, d54881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro883 q ha hb
  have h2 (q : Pattern) (ha : d54207 q = 1) (hb : d54882 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54207, d54882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54207, d54882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54208 q = 1) (hb : d54883 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54208, d54883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54208, d54883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54209 q = 1) (hb : d54884 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54209, d54884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54209, d54884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54210 q = 1) (hb : d54885 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54210, d54885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54210, d54885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54211 q = 1) (hb : d54886 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54211, d54886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54211, d54886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro885 (p : Pattern) (ha : d54213 p = 1) (hb : d54889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52479 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d800 q = 1) (hb : d52557 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d52557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro340 q ha hb
    | true =>
      simp only [d800, d52557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro341 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52570 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d801 q = 1) (hb : d52571 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d52571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d801, d52571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52572 q = 1) (hb : d53705 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52572, d53705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d52572, d53705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52573 q = 1) (hb : d53706 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52573, d53706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52573, d53706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52582 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d52583 q = 1) (hb : d54888 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52583, d54888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52583, d54888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d54213 q = 1) (hb : d54889 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54213, d54889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54213, d54889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  exact h9 p ha hb
theorem andIntro886 (p : Pattern) (ha : d54219 p = 1) (hb : d54895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54214 q = 1) (hb : d54890 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54214, d54890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54214, d54890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro885 q ha hb
  have h2 (q : Pattern) (ha : d54215 q = 1) (hb : d54891 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54215, d54891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54215, d54891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54216 q = 1) (hb : d54892 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54216, d54892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54216, d54892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54217 q = 1) (hb : d54893 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54217, d54893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54217, d54893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54218 q = 1) (hb : d54894 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54218, d54894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54218, d54894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54219 q = 1) (hb : d54895 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54219, d54895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54219, d54895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro887 (p : Pattern) (ha : d54222 p = 1) (hb : d54899 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1179 q = 1) (hb : d52837 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d52837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro346 q ha hb
    | true =>
      simp only [d1179, d52837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro347 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52850 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1180 q = 1) (hb : d52851 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d52851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1180, d52851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52852 q = 1) (hb : d53733 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52852, d53733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d52852, d53733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52853 q = 1) (hb : d53734 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52853, d53734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52853, d53734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52862 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d52863 q = 1) (hb : d54898 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52863, d54898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52863, d54898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d54222 q = 1) (hb : d54899 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54222, d54899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54222, d54899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  exact h9 p ha hb
theorem andIntro888 (p : Pattern) (ha : d54228 p = 1) (hb : d54905 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54223 q = 1) (hb : d54900 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54223, d54900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54223, d54900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro887 q ha hb
  have h2 (q : Pattern) (ha : d54224 q = 1) (hb : d54901 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54224, d54901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54224, d54901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54225 q = 1) (hb : d54902 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54225, d54902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54225, d54902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54226 q = 1) (hb : d54903 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54226, d54903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54226, d54903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54227 q = 1) (hb : d54904 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54227, d54904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54227, d54904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54228 q = 1) (hb : d54905 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54228, d54905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54228, d54905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro889 (p : Pattern) (ha : d54232 p = 1) (hb : d54910 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53083 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1640 q = 1) (hb : d53152 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d53152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro352 q ha hb
    | true =>
      simp only [d1640, d53152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro353 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53165 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1641 q = 1) (hb : d53166 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d53166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1641, d53166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53167 q = 1) (hb : d53762 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53167, d53762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d53167, d53762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d53168 q = 1) (hb : d53763 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53168, d53763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53168, d53763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d53177 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d53178 q = 1) (hb : d54909 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53178, d54909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53178, d54909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d54232 q = 1) (hb : d54910 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54232, d54910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54232, d54910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  exact h9 p ha hb
theorem andIntro890 (p : Pattern) (ha : d54238 p = 1) (hb : d54916 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54233 q = 1) (hb : d54911 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54233, d54911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54233, d54911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro889 q ha hb
  have h2 (q : Pattern) (ha : d54234 q = 1) (hb : d54912 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54234, d54912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54234, d54912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54235 q = 1) (hb : d54913 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54235, d54913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54235, d54913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54236 q = 1) (hb : d54914 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54236, d54914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54236, d54914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54237 q = 1) (hb : d54915 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54237, d54915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54237, d54915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54238 q = 1) (hb : d54916 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54238, d54916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54238, d54916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro891 (p : Pattern) (ha : d54243 p = 1) (hb : d54922 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53404 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2123 q = 1) (hb : d53469 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d53469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro358 q ha hb
    | true =>
      simp only [d2123, d53469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro359 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53482 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2124 q = 1) (hb : d53483 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d53483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2124, d53483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53484 q = 1) (hb : d53792 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53484, d53792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d53484, d53792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d53485 q = 1) (hb : d53793 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53485, d53793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53485, d53793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d53494 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d53495 q = 1) (hb : d54921 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53495, d54921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53495, d54921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d54243 q = 1) (hb : d54922 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54243, d54922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54243, d54922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  exact h9 p ha hb
theorem andIntro892 (p : Pattern) (ha : d54249 p = 1) (hb : d54928 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54244 q = 1) (hb : d54923 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54244, d54923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54244, d54923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro891 q ha hb
  have h2 (q : Pattern) (ha : d54245 q = 1) (hb : d54924 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54245, d54924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54245, d54924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54246 q = 1) (hb : d54925 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54246, d54925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54246, d54925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54247 q = 1) (hb : d54926 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54247, d54926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54247, d54926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54248 q = 1) (hb : d54927 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54248, d54927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54248, d54927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54249 q = 1) (hb : d54928 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54249, d54928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54249, d54928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro893 (p : Pattern) (ha : d54255 p = 1) (hb : d54934 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d54212 q = 1) (hb : d54887 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54212, d54887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro882 q ha hb
    | true =>
      simp only [d54212, d54887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro884 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54220 q = 1) (hb : d54896 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54220, d54896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54220, d54896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro886 q ha hb
  have h3 (q : Pattern) (ha : d54221 q = 1) (hb : d54897 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54221, d54897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54221, d54897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54229 q = 1) (hb : d54906 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54229, d54906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54229, d54906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro888 q ha hb
  have h5 (q : Pattern) (ha : d54230 q = 1) (hb : d54907 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54230, d54907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54230, d54907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54231 q = 1) (hb : d54908 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54231, d54908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54231, d54908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54239 q = 1) (hb : d54917 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54239, d54917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54239, d54917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro890 q ha hb
  have h8 (q : Pattern) (ha : d54240 q = 1) (hb : d54918 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54240, d54918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54240, d54918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54241 q = 1) (hb : d54919 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54241, d54919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54241, d54919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54242 q = 1) (hb : d54920 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54242, d54920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54242, d54920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54250 q = 1) (hb : d54929 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54250, d54929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54250, d54929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro892 q ha hb
  have h12 (q : Pattern) (ha : d54251 q = 1) (hb : d54930 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54251, d54930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54251, d54930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54252 q = 1) (hb : d54931 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54252, d54931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54252, d54931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54253 q = 1) (hb : d54932 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54253, d54932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54253, d54932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54254 q = 1) (hb : d54933 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54254, d54933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54254, d54933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54255 q = 1) (hb : d54934 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d54255, d54934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54255, d54934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro894 (p : Pattern) (ha : d54261 p = 1) (hb : d54940 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54256 q = 1) (hb : d54935 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54256, d54935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro893 q ha hb
    | true =>
      simp only [d54256, d54935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54257 q = 1) (hb : d54936 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54257, d54936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54257, d54936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54258 q = 1) (hb : d54937 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54258, d54937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54258, d54937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54259 q = 1) (hb : d54938 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54259, d54938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54259, d54938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54260 q = 1) (hb : d54939 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54260, d54939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54260, d54939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54261 q = 1) (hb : d54940 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d54261, d54940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54261, d54940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro895 (p : Pattern) (ha : d54267 p = 1) (hb : d54946 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54262 q = 1) (hb : d54941 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54262, d54941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro894 q ha hb
    | true =>
      simp only [d54262, d54941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54263 q = 1) (hb : d54942 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54263, d54942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54263, d54942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54264 q = 1) (hb : d54943 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54264, d54943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54264, d54943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54265 q = 1) (hb : d54944 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54265, d54944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54265, d54944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54266 q = 1) (hb : d54945 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54266, d54945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54266, d54945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54267 q = 1) (hb : d54946 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d54267, d54946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54267, d54946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro896 (p : Pattern) (ha : d54273 p = 1) (hb : d54952 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54268 q = 1) (hb : d54947 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54268, d54947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro895 q ha hb
    | true =>
      simp only [d54268, d54947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54269 q = 1) (hb : d54948 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54269, d54948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54269, d54948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54270 q = 1) (hb : d54949 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54270, d54949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54270, d54949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54271 q = 1) (hb : d54950 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54271, d54950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54271, d54950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54272 q = 1) (hb : d54951 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54272, d54951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54272, d54951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54273 q = 1) (hb : d54952 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d54273, d54952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54273, d54952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro897 (p : Pattern) (ha : d54279 p = 1) (hb : d54958 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54274 q = 1) (hb : d54953 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54274, d54953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro896 q ha hb
    | true =>
      simp only [d54274, d54953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54275 q = 1) (hb : d54954 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54275, d54954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54275, d54954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54276 q = 1) (hb : d54955 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54276, d54955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54276, d54955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54277 q = 1) (hb : d54956 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54277, d54956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54277, d54956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54278 q = 1) (hb : d54957 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54278, d54957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54278, d54957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54279 q = 1) (hb : d54958 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d54279, d54958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54279, d54958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro898 (p : Pattern) (ha : d54285 p = 1) (hb : d54964 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54280 q = 1) (hb : d54959 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54280, d54959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro897 q ha hb
    | true =>
      simp only [d54280, d54959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54281 q = 1) (hb : d54960 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54281, d54960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54281, d54960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54282 q = 1) (hb : d54961 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54282, d54961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54282, d54961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54283 q = 1) (hb : d54962 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54283, d54962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54283, d54962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54284 q = 1) (hb : d54963 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54284, d54963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54284, d54963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54285 q = 1) (hb : d54964 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d54285, d54964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54285, d54964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro899 (p : Pattern) (ha : d54291 p = 1) (hb : d54970 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54286 q = 1) (hb : d54965 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54286, d54965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro898 q ha hb
    | true =>
      simp only [d54286, d54965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54287 q = 1) (hb : d54966 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54287, d54966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54287, d54966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54288 q = 1) (hb : d54967 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54288, d54967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54288, d54967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54289 q = 1) (hb : d54968 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54289, d54968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54289, d54968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54290 q = 1) (hb : d54969 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54290, d54969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54290, d54969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54291 q = 1) (hb : d54970 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54291, d54970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54291, d54970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro900 (p : Pattern) (ha : d54297 p = 1) (hb : d54976 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54292 q = 1) (hb : d54971 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54292, d54971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro899 q ha hb
    | true =>
      simp only [d54292, d54971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54293 q = 1) (hb : d54972 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54293, d54972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54293, d54972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54294 q = 1) (hb : d54973 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54294, d54973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54294, d54973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54295 q = 1) (hb : d54974 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54295, d54974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54295, d54974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54296 q = 1) (hb : d54975 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54296, d54975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54296, d54975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54297 q = 1) (hb : d54976 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54297, d54976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54297, d54976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro901 (p : Pattern) (ha : d54298 p = 1) (hb : d54865 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d114 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d51647 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d51647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro372 q ha hb
    | true =>
      simp only [d112, d51647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro373 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d214 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113 q = 1) (hb : d51648 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d51648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, d51648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51649 q = 1) (hb : d53637 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51649, d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d51649, d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51650 q = 1) (hb : d53638 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51650, d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51650, d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d4353 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d51651 q = 1) (hb : d54864 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51651, d54864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51651, d54864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d54298 q = 1) (hb : d54865 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54298, d54865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54298, d54865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro902 (p : Pattern) (ha : d54304 p = 1) (hb : d54872 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d294 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292 q = 1) (hb : d51664 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d51664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro377 q ha hb
    | true =>
      simp only [d292, d51664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro378 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d398 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d293 q = 1) (hb : d51665 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d51665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293, d51665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51666 q = 1) (hb : d53653 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51666, d53653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d51666, d53653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51667 q = 1) (hb : d53654 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51667, d53654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51667, d53654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d51670 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d51671 q = 1) (hb : d54871 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51671, d54871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51671, d54871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d54304 q = 1) (hb : d54872 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54304, d54872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54304, d54872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro903 (p : Pattern) (ha : d54310 p = 1) (hb : d54878 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2676 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54299 q = 1) (hb : d54866 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54299, d54866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54299, d54866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro901 q ha hb
  have h3 (q : Pattern) (ha : d54300 q = 1) (hb : d54867 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54300, d54867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54300, d54867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54301 q = 1) (hb : d54868 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54301, d54868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54301, d54868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54302 q = 1) (hb : d54869 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54302, d54869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54302, d54869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54303 q = 1) (hb : d54870 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54303, d54870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54303, d54870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54305 q = 1) (hb : d54873 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54305, d54873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54305, d54873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro902 q ha hb
  have h8 (q : Pattern) (ha : d54306 q = 1) (hb : d54874 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54306, d54874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54306, d54874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54307 q = 1) (hb : d54875 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54307, d54875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54307, d54875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54308 q = 1) (hb : d54876 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54308, d54876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54308, d54876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54309 q = 1) (hb : d54877 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54309, d54877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54309, d54877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54310 q = 1) (hb : d54878 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54310, d54878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54310, d54878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro904 (p : Pattern) (ha : d54311 p = 1) (hb : d54880 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d510 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d508 q = 1) (hb : d51689 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d51689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro383 q ha hb
    | true =>
      simp only [d508, d51689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro384 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d645 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d509 q = 1) (hb : d51690 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d51690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d509, d51690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51691 q = 1) (hb : d53678 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51691, d53678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d51691, d53678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51692 q = 1) (hb : d53679 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51692, d53679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51692, d53679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d51695 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d51696 q = 1) (hb : d54879 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51696, d54879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51696, d54879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d54311 q = 1) (hb : d54880 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54311, d54880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54311, d54880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro905 (p : Pattern) (ha : d54317 p = 1) (hb : d54886 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54312 q = 1) (hb : d54881 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54312, d54881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54312, d54881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro904 q ha hb
  have h2 (q : Pattern) (ha : d54313 q = 1) (hb : d54882 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54313, d54882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54313, d54882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54314 q = 1) (hb : d54883 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54314, d54883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54314, d54883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54315 q = 1) (hb : d54884 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54315, d54884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54315, d54884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54316 q = 1) (hb : d54885 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54316, d54885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54316, d54885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54317 q = 1) (hb : d54886 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54317, d54886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54317, d54886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro906 (p : Pattern) (ha : d54319 p = 1) (hb : d54889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d802 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d800 q = 1) (hb : d51715 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d51715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro389 q ha hb
    | true =>
      simp only [d800, d51715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro390 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d951 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d801 q = 1) (hb : d51716 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d51716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d801, d51716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51717 q = 1) (hb : d53705 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51717, d53705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d51717, d53705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51718 q = 1) (hb : d53706 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51718, d53706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51718, d53706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d51721 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d51722 q = 1) (hb : d54888 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51722, d54888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51722, d54888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d54319 q = 1) (hb : d54889 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54319, d54889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54319, d54889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro907 (p : Pattern) (ha : d54325 p = 1) (hb : d54895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54320 q = 1) (hb : d54890 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54320, d54890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54320, d54890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro906 q ha hb
  have h2 (q : Pattern) (ha : d54321 q = 1) (hb : d54891 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54321, d54891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54321, d54891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54322 q = 1) (hb : d54892 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54322, d54892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54322, d54892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54323 q = 1) (hb : d54893 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54323, d54893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54323, d54893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54324 q = 1) (hb : d54894 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54324, d54894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54324, d54894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54325 q = 1) (hb : d54895 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54325, d54895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54325, d54895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro908 (p : Pattern) (ha : d54328 p = 1) (hb : d54899 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1181 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1179 q = 1) (hb : d51742 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d51742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro395 q ha hb
    | true =>
      simp only [d1179, d51742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro396 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1362 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1180 q = 1) (hb : d51743 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d51743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1180, d51743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51744 q = 1) (hb : d53733 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51744, d53733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d51744, d53733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51745 q = 1) (hb : d53734 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51745, d53734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51745, d53734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d51748 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d51749 q = 1) (hb : d54898 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51749, d54898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51749, d54898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d54328 q = 1) (hb : d54899 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54328, d54899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54328, d54899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro909 (p : Pattern) (ha : d54334 p = 1) (hb : d54905 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54329 q = 1) (hb : d54900 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54329, d54900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54329, d54900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro908 q ha hb
  have h2 (q : Pattern) (ha : d54330 q = 1) (hb : d54901 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54330, d54901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54330, d54901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54331 q = 1) (hb : d54902 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54331, d54902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54331, d54902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54332 q = 1) (hb : d54903 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54332, d54903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54332, d54903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54333 q = 1) (hb : d54904 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54333, d54904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54333, d54904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54334 q = 1) (hb : d54905 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54334, d54905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54334, d54905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro910 (p : Pattern) (ha : d54338 p = 1) (hb : d54910 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1642 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1640 q = 1) (hb : d51770 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d51770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro401 q ha hb
    | true =>
      simp only [d1640, d51770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro402 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1839 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1641 q = 1) (hb : d51771 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d51771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1641, d51771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51772 q = 1) (hb : d53762 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51772, d53762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d51772, d53762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51773 q = 1) (hb : d53763 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51773, d53763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51773, d53763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d51776 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d51777 q = 1) (hb : d54909 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51777, d54909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51777, d54909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d54338 q = 1) (hb : d54910 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54338, d54910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54338, d54910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro911 (p : Pattern) (ha : d54344 p = 1) (hb : d54916 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54339 q = 1) (hb : d54911 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54339, d54911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54339, d54911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro910 q ha hb
  have h2 (q : Pattern) (ha : d54340 q = 1) (hb : d54912 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54340, d54912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54340, d54912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54341 q = 1) (hb : d54913 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54341, d54913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54341, d54913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54342 q = 1) (hb : d54914 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54342, d54914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54342, d54914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54343 q = 1) (hb : d54915 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54343, d54915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54343, d54915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54344 q = 1) (hb : d54916 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54344, d54916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54344, d54916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro912 (p : Pattern) (ha : d54349 p = 1) (hb : d54922 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2125 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2123 q = 1) (hb : d51799 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d51799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro407 q ha hb
    | true =>
      simp only [d2123, d51799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro408 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2317 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2124 q = 1) (hb : d51800 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d51800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2124, d51800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51801 q = 1) (hb : d53792 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51801, d53792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d51801, d53792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51802 q = 1) (hb : d53793 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51802, d53793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51802, d53793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d51805 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d51806 q = 1) (hb : d54921 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51806, d54921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51806, d54921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d54349 q = 1) (hb : d54922 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54349, d54922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54349, d54922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro913 (p : Pattern) (ha : d54355 p = 1) (hb : d54928 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54350 q = 1) (hb : d54923 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54350, d54923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54350, d54923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro912 q ha hb
  have h2 (q : Pattern) (ha : d54351 q = 1) (hb : d54924 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54351, d54924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54351, d54924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54352 q = 1) (hb : d54925 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54352, d54925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54352, d54925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54353 q = 1) (hb : d54926 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54353, d54926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54353, d54926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54354 q = 1) (hb : d54927 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54354, d54927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54354, d54927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54355 q = 1) (hb : d54928 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54355, d54928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54355, d54928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro914 (p : Pattern) (ha : d54361 p = 1) (hb : d54934 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d54318 q = 1) (hb : d54887 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54318, d54887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro903 q ha hb
    | true =>
      simp only [d54318, d54887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro905 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54326 q = 1) (hb : d54896 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54326, d54896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54326, d54896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro907 q ha hb
  have h3 (q : Pattern) (ha : d54327 q = 1) (hb : d54897 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54327, d54897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54327, d54897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54335 q = 1) (hb : d54906 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54335, d54906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54335, d54906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro909 q ha hb
  have h5 (q : Pattern) (ha : d54336 q = 1) (hb : d54907 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54336, d54907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54336, d54907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54337 q = 1) (hb : d54908 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54337, d54908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54337, d54908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54345 q = 1) (hb : d54917 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54345, d54917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54345, d54917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro911 q ha hb
  have h8 (q : Pattern) (ha : d54346 q = 1) (hb : d54918 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54346, d54918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54346, d54918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54347 q = 1) (hb : d54919 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54347, d54919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54347, d54919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54348 q = 1) (hb : d54920 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54348, d54920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54348, d54920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54356 q = 1) (hb : d54929 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54356, d54929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54356, d54929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro913 q ha hb
  have h12 (q : Pattern) (ha : d54357 q = 1) (hb : d54930 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54357, d54930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54357, d54930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54358 q = 1) (hb : d54931 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54358, d54931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54358, d54931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54359 q = 1) (hb : d54932 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54359, d54932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54359, d54932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54360 q = 1) (hb : d54933 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54360, d54933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54360, d54933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54361 q = 1) (hb : d54934 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d54361, d54934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54361, d54934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro915 (p : Pattern) (ha : d54367 p = 1) (hb : d54940 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54362 q = 1) (hb : d54935 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54362, d54935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro914 q ha hb
    | true =>
      simp only [d54362, d54935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54363 q = 1) (hb : d54936 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54363, d54936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54363, d54936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54364 q = 1) (hb : d54937 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54364, d54937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54364, d54937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54365 q = 1) (hb : d54938 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54365, d54938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54365, d54938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54366 q = 1) (hb : d54939 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54366, d54939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54366, d54939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54367 q = 1) (hb : d54940 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d54367, d54940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54367, d54940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro916 (p : Pattern) (ha : d54373 p = 1) (hb : d54946 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54368 q = 1) (hb : d54941 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54368, d54941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro915 q ha hb
    | true =>
      simp only [d54368, d54941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54369 q = 1) (hb : d54942 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54369, d54942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54369, d54942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54370 q = 1) (hb : d54943 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54370, d54943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54370, d54943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54371 q = 1) (hb : d54944 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54371, d54944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54371, d54944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54372 q = 1) (hb : d54945 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54372, d54945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54372, d54945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54373 q = 1) (hb : d54946 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d54373, d54946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54373, d54946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro917 (p : Pattern) (ha : d54379 p = 1) (hb : d54952 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54374 q = 1) (hb : d54947 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54374, d54947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro916 q ha hb
    | true =>
      simp only [d54374, d54947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54375 q = 1) (hb : d54948 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54375, d54948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54375, d54948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54376 q = 1) (hb : d54949 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54376, d54949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54376, d54949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54377 q = 1) (hb : d54950 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54377, d54950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54377, d54950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54378 q = 1) (hb : d54951 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54378, d54951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54378, d54951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54379 q = 1) (hb : d54952 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d54379, d54952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54379, d54952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro918 (p : Pattern) (ha : d54385 p = 1) (hb : d54958 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54380 q = 1) (hb : d54953 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54380, d54953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro917 q ha hb
    | true =>
      simp only [d54380, d54953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54381 q = 1) (hb : d54954 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54381, d54954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54381, d54954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54382 q = 1) (hb : d54955 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54382, d54955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54382, d54955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54383 q = 1) (hb : d54956 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54383, d54956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54383, d54956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54384 q = 1) (hb : d54957 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54384, d54957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54384, d54957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54385 q = 1) (hb : d54958 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d54385, d54958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54385, d54958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro919 (p : Pattern) (ha : d54391 p = 1) (hb : d54964 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54386 q = 1) (hb : d54959 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54386, d54959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro918 q ha hb
    | true =>
      simp only [d54386, d54959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54387 q = 1) (hb : d54960 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54387, d54960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54387, d54960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54388 q = 1) (hb : d54961 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54388, d54961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54388, d54961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54389 q = 1) (hb : d54962 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54389, d54962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54389, d54962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54390 q = 1) (hb : d54963 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54390, d54963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54390, d54963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54391 q = 1) (hb : d54964 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d54391, d54964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54391, d54964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro920 (p : Pattern) (ha : d54397 p = 1) (hb : d54970 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54392 q = 1) (hb : d54965 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54392, d54965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro919 q ha hb
    | true =>
      simp only [d54392, d54965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54393 q = 1) (hb : d54966 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54393, d54966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54393, d54966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54394 q = 1) (hb : d54967 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54394, d54967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54394, d54967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54395 q = 1) (hb : d54968 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54395, d54968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54395, d54968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54396 q = 1) (hb : d54969 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54396, d54969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54396, d54969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54397 q = 1) (hb : d54970 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54397, d54970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54397, d54970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro921 (p : Pattern) (ha : d54403 p = 1) (hb : d54976 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54398 q = 1) (hb : d54971 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54398, d54971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro920 q ha hb
    | true =>
      simp only [d54398, d54971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54399 q = 1) (hb : d54972 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54399, d54972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54399, d54972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54400 q = 1) (hb : d54973 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54400, d54973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54400, d54973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54401 q = 1) (hb : d54974 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54401, d54974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54401, d54974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54402 q = 1) (hb : d54975 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54402, d54975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54402, d54975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54403 q = 1) (hb : d54976 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54403, d54976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54403, d54976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro922 (p : Pattern) (ha : d54631 p = 1) (hb : d55880 p = 1) : d3015 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54626 q = 1) (hb : d55754 q = 1) : d3010 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54626, d3010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro790 q ha hb
    | true =>
      simp only [d54626, d3010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54627 q = 1) (hb : d55754 q = 1) : d3011 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54627, d3011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54627, d3011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54628 q = 1) (hb : d55754 q = 1) : d3012 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54628, d3012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54628, d3012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d54629 q = 1) (hb : d55880 q = 1) : d3013 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54629, d55880, d3013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54629, d55880, d3013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d55880 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d54630 q = 1) (hb : d55880 q = 1) : d3014 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54630, d3014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54630, d3014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54631 q = 1) (hb : d55880 q = 1) : d3015 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54631, d3015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54631, d3015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro923 (p : Pattern) (ha : d54976 p = 1) (hb : d55880 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54971 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro832 q ha hb
    | true =>
      simp only [d54971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54972 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54973 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d54974 q = 1) (hb : d55880 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54974, d55880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54974, d55880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d55880 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d54975 q = 1) (hb : d55880 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54976 q = 1) (hb : d55880 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro924 (p : Pattern) (ha : d54631 p = 1) (hb : d55881 p = 1) : d54631 p = 1 := by
  have h0 (q : Pattern) (ha : d54631 q = 1) (hb : d55881 q = 1) : d54631 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro925 (p : Pattern) (ha : d54976 p = 1) (hb : d55881 p = 1) : d54976 p = 1 := by
  have h0 (q : Pattern) (ha : d54976 q = 1) (hb : d55881 q = 1) : d54976 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro926 (p : Pattern) (ha : d54631 p = 1) (hb : d55886 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54627 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d55883 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54628 q = 1) (hb : d55885 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54628, d55885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54628, d55885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54629 q = 1) (hb : d55886 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54629, d55886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54629, d55886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d55886 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54630 q = 1) (hb : d55886 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54631 q = 1) (hb : d55886 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h7 p ha hb
theorem andIntro927 (p : Pattern) (ha : d54976 p = 1) (hb : d55886 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54972 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d55883 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54973 q = 1) (hb : d55885 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54973, d55885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54973, d55885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54974 q = 1) (hb : d55886 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54974, d55886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54974, d55886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d55886 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54975 q = 1) (hb : d55886 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54976 q = 1) (hb : d55886 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h7 p ha hb
theorem andIntro928 (p : Pattern) (ha : d54520 p = 1) (hb : d55891 p = 1) : d56024 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d106 q = 1) : d106 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d114 q = 1) (hb : d55891 q = 1) : d3016 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, d55891, d3016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114, d55891, d3016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d51649 q = 1) (hb : d55891 q = 1) : d51649 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d51650 q = 1) (hb : d55891 q = 1) : d56022 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51650, d56022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51650, d56022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2528 q = 1) (hb : d55891 q = 1) : d2528 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54519 q = 1) (hb : d55891 q = 1) : d56023 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54519, d56023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54519, d56023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d55891 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54520 q = 1) (hb : d55891 q = 1) : d56024 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54520, d56024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54520, d56024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro929 (p : Pattern) (ha : d54527 p = 1) (hb : d55891 p = 1) : d56032 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d286 q = 1) : d286 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d293 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d294 q = 1) (hb : d55891 q = 1) : d3025 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, d55891, d3025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d294, d55891, d3025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d51666 q = 1) (hb : d55891 q = 1) : d51666 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d51667 q = 1) (hb : d55891 q = 1) : d56030 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51667, d56030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51667, d56030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2540 q = 1) (hb : d55891 q = 1) : d2540 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54526 q = 1) (hb : d55891 q = 1) : d56031 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54526, d56031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54526, d56031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d55891 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54527 q = 1) (hb : d55891 q = 1) : d56032 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54527, d56032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54527, d56032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro930 (p : Pattern) (ha : d54533 p = 1) (hb : d55891 p = 1) : d56038 p = 1 := by
  have h0 (q : Pattern) (ha : d2524 q = 1) (hb : d55891 q = 1) : d2524 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d55891 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54521 q = 1) (hb : d55891 q = 1) : d56025 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54521, d56025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54521, d56025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro928 q ha hb
  have h3 (q : Pattern) (ha : d54522 q = 1) (hb : d55891 q = 1) : d56026 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54522, d56026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54522, d56026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54523 q = 1) (hb : d55891 q = 1) : d56027 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54523, d56027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54523, d56027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54524 q = 1) (hb : d55891 q = 1) : d56028 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54524, d56028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54524, d56028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54525 q = 1) (hb : d55891 q = 1) : d56029 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54525, d56029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54525, d56029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54528 q = 1) (hb : d55891 q = 1) : d56033 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54528, d56033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54528, d56033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro929 q ha hb
  have h8 (q : Pattern) (ha : d54529 q = 1) (hb : d55891 q = 1) : d56034 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54529, d56034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54529, d56034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54530 q = 1) (hb : d55891 q = 1) : d56035 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54530, d56035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54530, d56035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54531 q = 1) (hb : d55891 q = 1) : d56036 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54531, d56036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54531, d56036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54532 q = 1) (hb : d55891 q = 1) : d56037 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54532, d56037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54532, d56037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54533 q = 1) (hb : d55891 q = 1) : d56038 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54533, d56038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54533, d56038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro931 (p : Pattern) (ha : d54535 p = 1) (hb : d55891 p = 1) : d56041 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d499 q = 1) : d499 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d509 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d510 q = 1) (hb : d55891 q = 1) : d3035 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d510, d55891, d3035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d510, d55891, d3035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d51691 q = 1) (hb : d55891 q = 1) : d51691 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d51692 q = 1) (hb : d55891 q = 1) : d56039 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51692, d56039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51692, d56039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2553 q = 1) (hb : d55891 q = 1) : d2553 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54534 q = 1) (hb : d55891 q = 1) : d56040 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54534, d56040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54534, d56040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d55891 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54535 q = 1) (hb : d55891 q = 1) : d56041 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54535, d56041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54535, d56041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro932 (p : Pattern) (ha : d54541 p = 1) (hb : d55891 p = 1) : d56047 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55891 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54536 q = 1) (hb : d55891 q = 1) : d56042 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54536, d56042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54536, d56042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro931 q ha hb
  have h2 (q : Pattern) (ha : d54537 q = 1) (hb : d55891 q = 1) : d56043 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54537, d56043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54537, d56043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54538 q = 1) (hb : d55891 q = 1) : d56044 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54538, d56044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54538, d56044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54539 q = 1) (hb : d55891 q = 1) : d56045 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54539, d56045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54539, d56045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54540 q = 1) (hb : d55891 q = 1) : d56046 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54540, d56046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54540, d56046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54541 q = 1) (hb : d55891 q = 1) : d56047 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54541, d56047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54541, d56047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro933 (p : Pattern) (ha : d54544 p = 1) (hb : d55891 p = 1) : d56051 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d791 q = 1) : d791 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d801 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d802 q = 1) (hb : d55891 q = 1) : d3046 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d802, d55891, d3046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d802, d55891, d3046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d51717 q = 1) (hb : d55891 q = 1) : d51717 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d51718 q = 1) (hb : d55891 q = 1) : d56049 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51718, d56049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51718, d56049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2567 q = 1) (hb : d55891 q = 1) : d2567 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54543 q = 1) (hb : d55891 q = 1) : d56050 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54543, d56050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54543, d56050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d55891 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54544 q = 1) (hb : d55891 q = 1) : d56051 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54544, d56051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54544, d56051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro934 (p : Pattern) (ha : d54550 p = 1) (hb : d55891 p = 1) : d56057 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55891 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54545 q = 1) (hb : d55891 q = 1) : d56052 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54545, d56052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54545, d56052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro933 q ha hb
  have h2 (q : Pattern) (ha : d54546 q = 1) (hb : d55891 q = 1) : d56053 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54546, d56053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54546, d56053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54547 q = 1) (hb : d55891 q = 1) : d56054 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54547, d56054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54547, d56054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54548 q = 1) (hb : d55891 q = 1) : d56055 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54548, d56055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54548, d56055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54549 q = 1) (hb : d55891 q = 1) : d56056 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54549, d56056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54549, d56056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54550 q = 1) (hb : d55891 q = 1) : d56057 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54550, d56057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54550, d56057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro935 (p : Pattern) (ha : d54554 p = 1) (hb : d55891 p = 1) : d56062 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1170 q = 1) : d1170 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1180 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1181 q = 1) (hb : d55891 q = 1) : d3058 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1181, d55891, d3058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1181, d55891, d3058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d51744 q = 1) (hb : d55891 q = 1) : d51744 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d51745 q = 1) (hb : d55891 q = 1) : d56060 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51745, d56060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51745, d56060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2582 q = 1) (hb : d55891 q = 1) : d2582 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54553 q = 1) (hb : d55891 q = 1) : d56061 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54553, d56061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54553, d56061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d55891 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54554 q = 1) (hb : d55891 q = 1) : d56062 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54554, d56062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54554, d56062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro936 (p : Pattern) (ha : d54560 p = 1) (hb : d55891 p = 1) : d56068 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55891 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54555 q = 1) (hb : d55891 q = 1) : d56063 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54555, d56063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54555, d56063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro935 q ha hb
  have h2 (q : Pattern) (ha : d54556 q = 1) (hb : d55891 q = 1) : d56064 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54556, d56064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54556, d56064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54557 q = 1) (hb : d55891 q = 1) : d56065 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54557, d56065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54557, d56065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54558 q = 1) (hb : d55891 q = 1) : d56066 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54558, d56066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54558, d56066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54559 q = 1) (hb : d55891 q = 1) : d56067 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54559, d56067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54559, d56067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54560 q = 1) (hb : d55891 q = 1) : d56068 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54560, d56068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54560, d56068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro937 (p : Pattern) (ha : d54565 p = 1) (hb : d55891 p = 1) : d56074 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1631 q = 1) : d1631 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1641 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1642 q = 1) (hb : d55891 q = 1) : d3071 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1642, d55891, d3071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1642, d55891, d3071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d51772 q = 1) (hb : d55891 q = 1) : d51772 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d51773 q = 1) (hb : d55891 q = 1) : d56072 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51773, d56072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51773, d56072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2598 q = 1) (hb : d55891 q = 1) : d2598 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54564 q = 1) (hb : d55891 q = 1) : d56073 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54564, d56073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54564, d56073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d55891 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54565 q = 1) (hb : d55891 q = 1) : d56074 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54565, d56074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54565, d56074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro938 (p : Pattern) (ha : d54571 p = 1) (hb : d55891 p = 1) : d56080 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55891 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54566 q = 1) (hb : d55891 q = 1) : d56075 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54566, d56075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54566, d56075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro937 q ha hb
  have h2 (q : Pattern) (ha : d54567 q = 1) (hb : d55891 q = 1) : d56076 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54567, d56076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54567, d56076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54568 q = 1) (hb : d55891 q = 1) : d56077 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54568, d56077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54568, d56077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54569 q = 1) (hb : d55891 q = 1) : d56078 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54569, d56078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54569, d56078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54570 q = 1) (hb : d55891 q = 1) : d56079 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54570, d56079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54570, d56079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54571 q = 1) (hb : d55891 q = 1) : d56080 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54571, d56080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54571, d56080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro939 (p : Pattern) (ha : d54577 p = 1) (hb : d55891 p = 1) : d56087 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2114 q = 1) : d2114 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2124 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2125 q = 1) (hb : d55891 q = 1) : d3085 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2125, d55891, d3085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2125, d55891, d3085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d51801 q = 1) (hb : d55891 q = 1) : d51801 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d51802 q = 1) (hb : d55891 q = 1) : d56085 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51802, d56085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51802, d56085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2615 q = 1) (hb : d55891 q = 1) : d2615 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54576 q = 1) (hb : d55891 q = 1) : d56086 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54576, d56086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54576, d56086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d55891 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54577 q = 1) (hb : d55891 q = 1) : d56087 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54577, d56087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54577, d56087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro940 (p : Pattern) (ha : d54583 p = 1) (hb : d55891 p = 1) : d56093 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55891 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54578 q = 1) (hb : d55891 q = 1) : d56088 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54578, d56088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54578, d56088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro939 q ha hb
  have h2 (q : Pattern) (ha : d54579 q = 1) (hb : d55891 q = 1) : d56089 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54579, d56089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54579, d56089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54580 q = 1) (hb : d55891 q = 1) : d56090 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54580, d56090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54580, d56090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54581 q = 1) (hb : d55891 q = 1) : d56091 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54581, d56091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54581, d56091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54582 q = 1) (hb : d55891 q = 1) : d56092 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54582, d56092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54582, d56092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54583 q = 1) (hb : d55891 q = 1) : d56093 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54583, d56093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54583, d56093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro941 (p : Pattern) (ha : d54589 p = 1) (hb : d55891 p = 1) : d56099 p = 1 := by
  have h0 (q : Pattern) (ha : d54542 q = 1) (hb : d55891 q = 1) : d56048 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54542, d56048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro930 q ha hb
    | true =>
      simp only [d54542, d56048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro932 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d55891 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54551 q = 1) (hb : d55891 q = 1) : d56058 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54551, d56058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54551, d56058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro934 q ha hb
  have h3 (q : Pattern) (ha : d54552 q = 1) (hb : d55891 q = 1) : d56059 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54552, d56059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54552, d56059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54561 q = 1) (hb : d55891 q = 1) : d56069 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54561, d56069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54561, d56069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro936 q ha hb
  have h5 (q : Pattern) (ha : d54562 q = 1) (hb : d55891 q = 1) : d56070 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54562, d56070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54562, d56070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54563 q = 1) (hb : d55891 q = 1) : d56071 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54563, d56071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54563, d56071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54572 q = 1) (hb : d55891 q = 1) : d56081 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54572, d56081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54572, d56081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro938 q ha hb
  have h8 (q : Pattern) (ha : d54573 q = 1) (hb : d55891 q = 1) : d56082 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54573, d56082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54573, d56082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54574 q = 1) (hb : d55891 q = 1) : d56083 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54574, d56083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54574, d56083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54575 q = 1) (hb : d55891 q = 1) : d56084 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54575, d56084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54575, d56084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54584 q = 1) (hb : d55891 q = 1) : d56094 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54584, d56094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54584, d56094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro940 q ha hb
  have h12 (q : Pattern) (ha : d54585 q = 1) (hb : d55891 q = 1) : d56095 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54585, d56095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54585, d56095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54586 q = 1) (hb : d55891 q = 1) : d56096 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54586, d56096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54586, d56096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54587 q = 1) (hb : d55891 q = 1) : d56097 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54587, d56097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54587, d56097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54588 q = 1) (hb : d55891 q = 1) : d56098 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54588, d56098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54588, d56098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54589 q = 1) (hb : d55891 q = 1) : d56099 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d54589, d56099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54589, d56099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro942 (p : Pattern) (ha : d54595 p = 1) (hb : d55891 p = 1) : d56105 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55891 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54590 q = 1) (hb : d55891 q = 1) : d56100 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54590, d56100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro941 q ha hb
    | true =>
      simp only [d54590, d56100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54591 q = 1) (hb : d55891 q = 1) : d56101 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54591, d56101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54591, d56101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54592 q = 1) (hb : d55891 q = 1) : d56102 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54592, d56102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54592, d56102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54593 q = 1) (hb : d55891 q = 1) : d56103 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54593, d56103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54593, d56103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54594 q = 1) (hb : d55891 q = 1) : d56104 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54594, d56104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54594, d56104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54595 q = 1) (hb : d55891 q = 1) : d56105 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d54595, d56105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54595, d56105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro943 (p : Pattern) (ha : d54601 p = 1) (hb : d55891 p = 1) : d56111 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55891 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54596 q = 1) (hb : d55891 q = 1) : d56106 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54596, d56106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro942 q ha hb
    | true =>
      simp only [d54596, d56106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54597 q = 1) (hb : d55891 q = 1) : d56107 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54597, d56107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54597, d56107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54598 q = 1) (hb : d55891 q = 1) : d56108 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54598, d56108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54598, d56108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54599 q = 1) (hb : d55891 q = 1) : d56109 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54599, d56109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54599, d56109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54600 q = 1) (hb : d55891 q = 1) : d56110 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54600, d56110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54600, d56110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54601 q = 1) (hb : d55891 q = 1) : d56111 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d54601, d56111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54601, d56111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro944 (p : Pattern) (ha : d54607 p = 1) (hb : d55891 p = 1) : d56117 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55891 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54602 q = 1) (hb : d55891 q = 1) : d56112 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54602, d56112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro943 q ha hb
    | true =>
      simp only [d54602, d56112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54603 q = 1) (hb : d55891 q = 1) : d56113 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54603, d56113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54603, d56113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54604 q = 1) (hb : d55891 q = 1) : d56114 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54604, d56114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54604, d56114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54605 q = 1) (hb : d55891 q = 1) : d56115 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54605, d56115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54605, d56115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54606 q = 1) (hb : d55891 q = 1) : d56116 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54606, d56116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54606, d56116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54607 q = 1) (hb : d55891 q = 1) : d56117 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d54607, d56117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54607, d56117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro945 (p : Pattern) (ha : d54613 p = 1) (hb : d55891 p = 1) : d56123 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55891 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54608 q = 1) (hb : d55891 q = 1) : d56118 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54608, d56118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro944 q ha hb
    | true =>
      simp only [d54608, d56118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54609 q = 1) (hb : d55891 q = 1) : d56119 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54609, d56119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54609, d56119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54610 q = 1) (hb : d55891 q = 1) : d56120 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54610, d56120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54610, d56120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54611 q = 1) (hb : d55891 q = 1) : d56121 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54611, d56121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54611, d56121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54612 q = 1) (hb : d55891 q = 1) : d56122 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54612, d56122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54612, d56122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54613 q = 1) (hb : d55891 q = 1) : d56123 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d54613, d56123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54613, d56123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro946 (p : Pattern) (ha : d54619 p = 1) (hb : d55891 p = 1) : d56129 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55891 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54614 q = 1) (hb : d55891 q = 1) : d56124 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54614, d56124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro945 q ha hb
    | true =>
      simp only [d54614, d56124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54615 q = 1) (hb : d55891 q = 1) : d56125 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54615, d56125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54615, d56125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54616 q = 1) (hb : d55891 q = 1) : d56126 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54616, d56126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54616, d56126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54617 q = 1) (hb : d55891 q = 1) : d56127 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54617, d56127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54617, d56127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54618 q = 1) (hb : d55891 q = 1) : d56128 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54618, d56128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54618, d56128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54619 q = 1) (hb : d55891 q = 1) : d56129 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d54619, d56129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54619, d56129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro947 (p : Pattern) (ha : d54625 p = 1) (hb : d55891 p = 1) : d56135 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55891 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54620 q = 1) (hb : d55891 q = 1) : d56130 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54620, d56130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro946 q ha hb
    | true =>
      simp only [d54620, d56130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54621 q = 1) (hb : d55891 q = 1) : d56131 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54621, d56131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54621, d56131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54622 q = 1) (hb : d55891 q = 1) : d56132 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54622, d56132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54622, d56132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54623 q = 1) (hb : d55891 q = 1) : d56133 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54623, d56133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54623, d56133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54624 q = 1) (hb : d55891 q = 1) : d56134 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54624, d56134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54624, d56134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54625 q = 1) (hb : d55891 q = 1) : d56135 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54625, d56135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54625, d56135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro948 (p : Pattern) (ha : d54631 p = 1) (hb : d55894 p = 1) : d56141 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55891 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54626 q = 1) (hb : d55891 q = 1) : d56136 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54626, d56136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro947 q ha hb
    | true =>
      simp only [d54626, d56136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54627 q = 1) (hb : d55891 q = 1) : d56137 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54627, d56137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54627, d56137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d55892 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54628 q = 1) (hb : d55893 q = 1) : d56138 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54628, d55893, d56138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54628, d55893, d56138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54629 q = 1) (hb : d55894 q = 1) : d56139 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54629, d55894, d56139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54629, d55894, d56139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d55894 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54630 q = 1) (hb : d55894 q = 1) : d56140 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54630, d56140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54630, d56140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54631 q = 1) (hb : d55894 q = 1) : d56141 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54631, d56141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54631, d56141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h9 p ha hb
theorem andIntro949 (p : Pattern) (ha : d55898 p = 1) (hb : d56024 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d51957 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, d51957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, d51957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d51958 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, d51958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, d51958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3016 q = 1) (hb : d55895 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3016, d55895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3016, d55895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51647 q = 1) (hb : d52030 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51647, d52030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31 q ha hb
    | true =>
      simp only [d51647, d52030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34 q ha hb
  have h5 (q : Pattern) (ha : d214 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17 q ha hb
    | true =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d51648 q = 1) (hb : d52033 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51648, d52033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51648, d52033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51649 q = 1) (hb : d52034 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51649, d52034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51649, d52034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d55896 q = 1) (hb : d56022 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d55896, d56022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d55896, d56022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d2525 q = 1) (hb : d55598 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2525, d55598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2525, d55598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17 q ha hb
  have h10 (q : Pattern) (ha : d2526 q = 1) (hb : d55599 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2526, d55599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2526, d55599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d2527 q = 1) (hb : d55600 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2527, d55600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2527, d55600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d2528 q = 1) (hb : d55601 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2528, d55601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2528, d55601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d55897 q = 1) (hb : d56023 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d55897, d56023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d55897, d56023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d55898 q = 1) (hb : d56024 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d55898, d56024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d55898, d56024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro950 (p : Pattern) (ha : d55907 p = 1) (hb : d56032 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d52084 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, d52084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, d52084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36 q ha hb
  have h2 (q : Pattern) (ha : d286 q = 1) (hb : d52085 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, d52085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, d52085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3025 q = 1) (hb : d55904 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3025, d55904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3025, d55904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51664 q = 1) (hb : d52162 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51664, d52162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54 q ha hb
    | true =>
      simp only [d51664, d52162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57 q ha hb
  have h5 (q : Pattern) (ha : d398 q = 1) (hb : d52164 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d398, d52164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38 q ha hb
    | true =>
      simp only [d398, d52164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q ha hb
  have h6 (q : Pattern) (ha : d51665 q = 1) (hb : d52165 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51665, d52165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51665, d52165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51666 q = 1) (hb : d52166 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51666, d52166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51666, d52166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d55905 q = 1) (hb : d56030 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d55905, d56030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d55905, d56030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d2537 q = 1) (hb : d55610 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2537, d55610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2537, d55610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro697 q ha hb
  have h10 (q : Pattern) (ha : d2538 q = 1) (hb : d55611 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2538, d55611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2538, d55611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d2539 q = 1) (hb : d55612 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2539, d55612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2539, d55612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d2540 q = 1) (hb : d55613 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2540, d55613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2540, d55613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d55906 q = 1) (hb : d56031 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d55906, d56031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d55906, d56031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d55907 q = 1) (hb : d56032 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d55907, d56032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d55907, d56032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro951 (p : Pattern) (ha : d55913 p = 1) (hb : d56038 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2521 q = 1) (hb : d54634 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2521, d54634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2521, d54634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro557 q ha hb
  have h2 (q : Pattern) (ha : d2522 q = 1) (hb : d54635 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2522, d54635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2522, d54635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2523 q = 1) (hb : d54636 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2523, d54636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2523, d54636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2524 q = 1) (hb : d54637 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2524, d54637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2524, d54637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d55899 q = 1) (hb : d56025 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d55899, d56025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55899, d56025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro949 q ha hb
  have h6 (q : Pattern) (ha : d55900 q = 1) (hb : d56026 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d55900, d56026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55900, d56026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d55901 q = 1) (hb : d56027 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d55901, d56027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55901, d56027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d55902 q = 1) (hb : d56028 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d55902, d56028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55902, d56028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d55903 q = 1) (hb : d56029 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d55903, d56029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d55903, d56029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d55908 q = 1) (hb : d56033 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d55908, d56033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55908, d56033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro950 q ha hb
  have h11 (q : Pattern) (ha : d55909 q = 1) (hb : d56034 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d55909, d56034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55909, d56034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d55910 q = 1) (hb : d56035 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d55910, d56035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55910, d56035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d55911 q = 1) (hb : d56036 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d55911, d56036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55911, d56036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d55912 q = 1) (hb : d56037 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d55912, d56037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55912, d56037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d55913 q = 1) (hb : d56038 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d55913, d56038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d55913, d56038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro952 (p : Pattern) (ha : d55917 p = 1) (hb : d56041 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d498 q = 1) (hb : d52245 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d498, d52245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d498, d52245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64 q ha hb
  have h2 (q : Pattern) (ha : d499 q = 1) (hb : d52246 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d499, d52246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d499, d52246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3035 q = 1) (hb : d55914 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3035, d55914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3035, d55914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51689 q = 1) (hb : d52336 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51689, d52336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92 q ha hb
    | true =>
      simp only [d51689, d52336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97 q ha hb
  have h5 (q : Pattern) (ha : d645 q = 1) (hb : d52349 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d645, d52349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68 q ha hb
    | true =>
      simp only [d645, d52349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69 q ha hb
  have h6 (q : Pattern) (ha : d51690 q = 1) (hb : d52350 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51690, d52350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51690, d52350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51691 q = 1) (hb : d52351 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51691, d52351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51691, d52351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d55915 q = 1) (hb : d56039 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d55915, d56039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d55915, d56039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d2550 q = 1) (hb : d55623 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2550, d55623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2550, d55623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro700 q ha hb
  have h10 (q : Pattern) (ha : d2551 q = 1) (hb : d55624 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2551, d55624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2551, d55624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d2552 q = 1) (hb : d55625 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2552, d55625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2552, d55625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d2553 q = 1) (hb : d55626 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2553, d55626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2553, d55626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d55916 q = 1) (hb : d56040 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d55916, d56040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d55916, d56040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d55917 q = 1) (hb : d56041 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d55917, d56041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d55917, d56041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro953 (p : Pattern) (ha : d55923 p = 1) (hb : d56047 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d55918 q = 1) (hb : d56042 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d55918, d56042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55918, d56042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro952 q ha hb
  have h2 (q : Pattern) (ha : d55919 q = 1) (hb : d56043 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d55919, d56043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55919, d56043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d55920 q = 1) (hb : d56044 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d55920, d56044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55920, d56044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d55921 q = 1) (hb : d56045 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d55921, d56045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55921, d56045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d55922 q = 1) (hb : d56046 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d55922, d56046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55922, d56046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d55923 q = 1) (hb : d56047 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d55923, d56047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55923, d56047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro954 (p : Pattern) (ha : d55928 p = 1) (hb : d56051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d790 q = 1) (hb : d52467 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d790, d52467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d790, d52467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108 q ha hb
  have h2 (q : Pattern) (ha : d791 q = 1) (hb : d52468 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d791, d52468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d791, d52468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3046 q = 1) (hb : d55925 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3046, d55925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3046, d55925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51715 q = 1) (hb : d52557 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51715, d52557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro139 q ha hb
    | true =>
      simp only [d51715, d52557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro144 q ha hb
  have h5 (q : Pattern) (ha : d951 q = 1) (hb : d52570 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d951, d52570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro112 q ha hb
    | true =>
      simp only [d951, d52570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro113 q ha hb
  have h6 (q : Pattern) (ha : d51716 q = 1) (hb : d52571 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51716, d52571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51716, d52571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51717 q = 1) (hb : d52572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51717, d52572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51717, d52572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d55926 q = 1) (hb : d56049 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d55926, d56049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d55926, d56049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d2564 q = 1) (hb : d55637 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2564, d55637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2564, d55637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro703 q ha hb
  have h10 (q : Pattern) (ha : d2565 q = 1) (hb : d55638 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2565, d55638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2565, d55638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d2566 q = 1) (hb : d55639 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2566, d55639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2566, d55639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d2567 q = 1) (hb : d55640 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2567, d55640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2567, d55640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d55927 q = 1) (hb : d56050 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d55927, d56050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d55927, d56050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d55928 q = 1) (hb : d56051 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d55928, d56051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d55928, d56051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro955 (p : Pattern) (ha : d55934 p = 1) (hb : d56057 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d55929 q = 1) (hb : d56052 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d55929, d56052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55929, d56052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro954 q ha hb
  have h2 (q : Pattern) (ha : d55930 q = 1) (hb : d56053 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d55930, d56053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55930, d56053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d55931 q = 1) (hb : d56054 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d55931, d56054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55931, d56054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d55932 q = 1) (hb : d56055 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d55932, d56055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55932, d56055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d55933 q = 1) (hb : d56056 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d55933, d56056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55933, d56056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d55934 q = 1) (hb : d56057 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d55934, d56057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55934, d56057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro956 (p : Pattern) (ha : d55940 p = 1) (hb : d56062 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1169 q = 1) (hb : d52750 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1169, d52750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1169, d52750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro160 q ha hb
  have h2 (q : Pattern) (ha : d1170 q = 1) (hb : d52751 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1170, d52751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1170, d52751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3058 q = 1) (hb : d55937 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3058, d55937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3058, d55937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51742 q = 1) (hb : d52837 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51742, d52837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro191 q ha hb
    | true =>
      simp only [d51742, d52837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro196 q ha hb
  have h5 (q : Pattern) (ha : d1362 q = 1) (hb : d52850 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1362, d52850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro164 q ha hb
    | true =>
      simp only [d1362, d52850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro165 q ha hb
  have h6 (q : Pattern) (ha : d51743 q = 1) (hb : d52851 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51743, d52851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51743, d52851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51744 q = 1) (hb : d52852 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51744, d52852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51744, d52852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d55938 q = 1) (hb : d56060 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d55938, d56060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d55938, d56060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d2579 q = 1) (hb : d55652 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2579, d55652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2579, d55652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro706 q ha hb
  have h10 (q : Pattern) (ha : d2580 q = 1) (hb : d55653 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2580, d55653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2580, d55653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d2581 q = 1) (hb : d55654 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2581, d55654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2581, d55654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d2582 q = 1) (hb : d55655 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2582, d55655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2582, d55655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d55939 q = 1) (hb : d56061 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d55939, d56061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d55939, d56061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d55940 q = 1) (hb : d56062 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d55940, d56062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d55940, d56062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro957 (p : Pattern) (ha : d55946 p = 1) (hb : d56068 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d55941 q = 1) (hb : d56063 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d55941, d56063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55941, d56063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro956 q ha hb
  have h2 (q : Pattern) (ha : d55942 q = 1) (hb : d56064 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d55942, d56064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55942, d56064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d55943 q = 1) (hb : d56065 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d55943, d56065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55943, d56065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d55944 q = 1) (hb : d56066 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d55944, d56066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55944, d56066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d55945 q = 1) (hb : d56067 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d55945, d56067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55945, d56067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d55946 q = 1) (hb : d56068 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d55946, d56068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55946, d56068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro958 (p : Pattern) (ha : d55953 p = 1) (hb : d56074 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1630 q = 1) (hb : d53071 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1630, d53071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1630, d53071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro218 q ha hb
  have h2 (q : Pattern) (ha : d1631 q = 1) (hb : d53072 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1631, d53072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1631, d53072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3071 q = 1) (hb : d55950 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3071, d55950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3071, d55950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51770 q = 1) (hb : d53152 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51770, d53152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro247 q ha hb
    | true =>
      simp only [d51770, d53152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro252 q ha hb
  have h5 (q : Pattern) (ha : d1839 q = 1) (hb : d53165 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1839, d53165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro222 q ha hb
    | true =>
      simp only [d1839, d53165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro223 q ha hb
  have h6 (q : Pattern) (ha : d51771 q = 1) (hb : d53166 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51771, d53166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51771, d53166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51772 q = 1) (hb : d53167 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51772, d53167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51772, d53167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d55951 q = 1) (hb : d56072 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d55951, d56072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d55951, d56072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d2595 q = 1) (hb : d55668 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2595, d55668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2595, d55668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro709 q ha hb
  have h10 (q : Pattern) (ha : d2596 q = 1) (hb : d55669 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2596, d55669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2596, d55669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d2597 q = 1) (hb : d55670 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2597, d55670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2597, d55670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d2598 q = 1) (hb : d55671 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2598, d55671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2598, d55671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d55952 q = 1) (hb : d56073 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d55952, d56073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d55952, d56073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d55953 q = 1) (hb : d56074 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d55953, d56074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d55953, d56074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro959 (p : Pattern) (ha : d55959 p = 1) (hb : d56080 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d55954 q = 1) (hb : d56075 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d55954, d56075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55954, d56075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro958 q ha hb
  have h2 (q : Pattern) (ha : d55955 q = 1) (hb : d56076 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d55955, d56076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55955, d56076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d55956 q = 1) (hb : d56077 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d55956, d56077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55956, d56077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d55957 q = 1) (hb : d56078 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d55957, d56078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55957, d56078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d55958 q = 1) (hb : d56079 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d55958, d56079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55958, d56079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d55959 q = 1) (hb : d56080 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d55959, d56080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55959, d56080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro960 (p : Pattern) (ha : d55967 p = 1) (hb : d56087 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2113 q = 1) (hb : d53392 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2113, d53392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2113, d53392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro277 q ha hb
  have h2 (q : Pattern) (ha : d2114 q = 1) (hb : d53393 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2114, d53393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2114, d53393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3085 q = 1) (hb : d55964 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3085, d55964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3085, d55964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51799 q = 1) (hb : d53469 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51799, d53469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro306 q ha hb
    | true =>
      simp only [d51799, d53469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro311 q ha hb
  have h5 (q : Pattern) (ha : d2317 q = 1) (hb : d53482 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2317, d53482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro281 q ha hb
    | true =>
      simp only [d2317, d53482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro282 q ha hb
  have h6 (q : Pattern) (ha : d51800 q = 1) (hb : d53483 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51800, d53483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51800, d53483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51801 q = 1) (hb : d53484 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51801, d53484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51801, d53484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d55965 q = 1) (hb : d56085 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d55965, d56085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d55965, d56085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d2612 q = 1) (hb : d55685 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2612, d55685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2612, d55685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro712 q ha hb
  have h10 (q : Pattern) (ha : d2613 q = 1) (hb : d55686 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2613, d55686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2613, d55686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d2614 q = 1) (hb : d55687 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2614, d55687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2614, d55687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d2615 q = 1) (hb : d55688 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2615, d55688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2615, d55688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d55966 q = 1) (hb : d56086 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d55966, d56086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d55966, d56086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d55967 q = 1) (hb : d56087 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d55967, d56087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d55967, d56087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro961 (p : Pattern) (ha : d55973 p = 1) (hb : d56093 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d55968 q = 1) (hb : d56088 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d55968, d56088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55968, d56088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro960 q ha hb
  have h2 (q : Pattern) (ha : d55969 q = 1) (hb : d56089 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d55969, d56089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55969, d56089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d55970 q = 1) (hb : d56090 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d55970, d56090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55970, d56090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d55971 q = 1) (hb : d56091 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d55971, d56091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55971, d56091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d55972 q = 1) (hb : d56092 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d55972, d56092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55972, d56092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d55973 q = 1) (hb : d56093 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d55973, d56093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55973, d56093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro962 (p : Pattern) (ha : d55979 p = 1) (hb : d56099 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d55924 q = 1) (hb : d56048 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d55924, d56048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro951 q ha hb
    | true =>
      simp only [d55924, d56048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro953 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d55935 q = 1) (hb : d56058 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d55935, d56058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d55935, d56058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro955 q ha hb
  have h3 (q : Pattern) (ha : d55936 q = 1) (hb : d56059 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d55936, d56059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d55936, d56059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d55947 q = 1) (hb : d56069 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d55947, d56069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d55947, d56069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro957 q ha hb
  have h5 (q : Pattern) (ha : d55948 q = 1) (hb : d56070 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d55948, d56070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d55948, d56070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d55949 q = 1) (hb : d56071 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d55949, d56071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d55949, d56071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d55960 q = 1) (hb : d56081 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d55960, d56081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d55960, d56081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro959 q ha hb
  have h8 (q : Pattern) (ha : d55961 q = 1) (hb : d56082 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d55961, d56082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d55961, d56082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d55962 q = 1) (hb : d56083 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d55962, d56083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d55962, d56083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d55963 q = 1) (hb : d56084 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d55963, d56084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d55963, d56084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d55974 q = 1) (hb : d56094 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d55974, d56094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d55974, d56094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro961 q ha hb
  have h12 (q : Pattern) (ha : d55975 q = 1) (hb : d56095 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d55975, d56095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d55975, d56095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d55976 q = 1) (hb : d56096 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d55976, d56096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d55976, d56096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d55977 q = 1) (hb : d56097 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d55977, d56097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d55977, d56097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d55978 q = 1) (hb : d56098 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d55978, d56098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d55978, d56098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d55979 q = 1) (hb : d56099 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d55979, d56099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d55979, d56099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro963 (p : Pattern) (ha : d55985 p = 1) (hb : d56105 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d55980 q = 1) (hb : d56100 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d55980, d56100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro962 q ha hb
    | true =>
      simp only [d55980, d56100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d55981 q = 1) (hb : d56101 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d55981, d56101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d55981, d56101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d55982 q = 1) (hb : d56102 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d55982, d56102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d55982, d56102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d55983 q = 1) (hb : d56103 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d55983, d56103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d55983, d56103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d55984 q = 1) (hb : d56104 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d55984, d56104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d55984, d56104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d55985 q = 1) (hb : d56105 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d55985, d56105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d55985, d56105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro964 (p : Pattern) (ha : d55991 p = 1) (hb : d56111 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d55986 q = 1) (hb : d56106 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d55986, d56106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro963 q ha hb
    | true =>
      simp only [d55986, d56106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d55987 q = 1) (hb : d56107 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d55987, d56107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d55987, d56107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d55988 q = 1) (hb : d56108 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d55988, d56108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d55988, d56108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d55989 q = 1) (hb : d56109 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d55989, d56109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d55989, d56109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d55990 q = 1) (hb : d56110 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d55990, d56110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d55990, d56110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d55991 q = 1) (hb : d56111 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d55991, d56111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d55991, d56111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro965 (p : Pattern) (ha : d55997 p = 1) (hb : d56117 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d55992 q = 1) (hb : d56112 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d55992, d56112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro964 q ha hb
    | true =>
      simp only [d55992, d56112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d55993 q = 1) (hb : d56113 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d55993, d56113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d55993, d56113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d55994 q = 1) (hb : d56114 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d55994, d56114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d55994, d56114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d55995 q = 1) (hb : d56115 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d55995, d56115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d55995, d56115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d55996 q = 1) (hb : d56116 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d55996, d56116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d55996, d56116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d55997 q = 1) (hb : d56117 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d55997, d56117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d55997, d56117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro966 (p : Pattern) (ha : d56003 p = 1) (hb : d56123 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d55998 q = 1) (hb : d56118 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d55998, d56118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro965 q ha hb
    | true =>
      simp only [d55998, d56118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d55999 q = 1) (hb : d56119 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d55999, d56119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d55999, d56119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d56000 q = 1) (hb : d56120 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d56000, d56120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d56000, d56120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d56001 q = 1) (hb : d56121 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d56001, d56121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d56001, d56121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d56002 q = 1) (hb : d56122 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d56002, d56122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d56002, d56122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d56003 q = 1) (hb : d56123 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d56003, d56123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d56003, d56123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro967 (p : Pattern) (ha : d56009 p = 1) (hb : d56129 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56004 q = 1) (hb : d56124 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d56004, d56124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro966 q ha hb
    | true =>
      simp only [d56004, d56124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d56005 q = 1) (hb : d56125 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d56005, d56125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d56005, d56125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d56006 q = 1) (hb : d56126 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d56006, d56126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d56006, d56126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d56007 q = 1) (hb : d56127 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d56007, d56127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d56007, d56127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d56008 q = 1) (hb : d56128 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d56008, d56128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d56008, d56128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d56009 q = 1) (hb : d56129 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d56009, d56129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d56009, d56129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro968 (p : Pattern) (ha : d56015 p = 1) (hb : d56135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56010 q = 1) (hb : d56130 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d56010, d56130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro967 q ha hb
    | true =>
      simp only [d56010, d56130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d56011 q = 1) (hb : d56131 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d56011, d56131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d56011, d56131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d56012 q = 1) (hb : d56132 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d56012, d56132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d56012, d56132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d56013 q = 1) (hb : d56133 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d56013, d56133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d56013, d56133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d56014 q = 1) (hb : d56134 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d56014, d56134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d56014, d56134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d56015 q = 1) (hb : d56135 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d56015, d56135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d56015, d56135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro969 (p : Pattern) (ha : d56021 p = 1) (hb : d56141 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56016 q = 1) (hb : d56136 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d56016, d56136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro968 q ha hb
    | true =>
      simp only [d56016, d56136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d56017 q = 1) (hb : d56137 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d56017, d56137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d56017, d56137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d56018 q = 1) (hb : d56138 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d56018, d56138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d56018, d56138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d56019 q = 1) (hb : d56139 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d56019, d56139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d56019, d56139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d56020 q = 1) (hb : d56140 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d56020, d56140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d56020, d56140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d56021 q = 1) (hb : d56141 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d56021, d56141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d56021, d56141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro970 (p : Pattern) (ha : d54976 p = 1) (hb : d55894 p = 1) : d54976 p = 1 := by
  have h0 (q : Pattern) (ha : d54976 q = 1) (hb : d55894 q = 1) : d54976 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro971 (p : Pattern) (ha : d54865 p = 1) (hb : d55898 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55895 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d52030 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d52030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro323 q ha hb
    | true =>
      simp only [d112, d52030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro324 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113 q = 1) (hb : d52033 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d52033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, d52033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52034 q = 1) (hb : d53637 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52034, d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d52034, d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d53638 q = 1) (hb : d55896 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, d55896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, d55896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d55601 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54864 q = 1) (hb : d55897 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54864, d55897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54864, d55897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54865 q = 1) (hb : d55898 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54865, d55898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54865, d55898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro972 (p : Pattern) (ha : d54872 p = 1) (hb : d55907 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55904 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292 q = 1) (hb : d52162 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d52162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro328 q ha hb
    | true =>
      simp only [d292, d52162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro329 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52164 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d293 q = 1) (hb : d52165 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d52165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293, d52165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52166 q = 1) (hb : d53653 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52166, d53653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d52166, d53653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d53654 q = 1) (hb : d55905 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, d55905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, d55905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d55613 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54871 q = 1) (hb : d55906 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54871, d55906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54871, d55906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54872 q = 1) (hb : d55907 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54872, d55907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54872, d55907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro973 (p : Pattern) (ha : d54878 p = 1) (hb : d55913 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54637 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54866 q = 1) (hb : d55899 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54866, d55899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54866, d55899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro971 q ha hb
  have h3 (q : Pattern) (ha : d54867 q = 1) (hb : d55900 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54867, d55900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54867, d55900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54868 q = 1) (hb : d55901 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54868, d55901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54868, d55901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54869 q = 1) (hb : d55902 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54869, d55902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54869, d55902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54870 q = 1) (hb : d55903 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54870, d55903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54870, d55903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54873 q = 1) (hb : d55908 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54873, d55908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54873, d55908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro972 q ha hb
  have h8 (q : Pattern) (ha : d54874 q = 1) (hb : d55909 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54874, d55909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54874, d55909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54875 q = 1) (hb : d55910 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54875, d55910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54875, d55910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54876 q = 1) (hb : d55911 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54876, d55911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54876, d55911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54877 q = 1) (hb : d55912 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54877, d55912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54877, d55912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54878 q = 1) (hb : d55913 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54878, d55913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54878, d55913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro974 (p : Pattern) (ha : d54880 p = 1) (hb : d55917 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55914 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d508 q = 1) (hb : d52336 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d52336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro334 q ha hb
    | true =>
      simp only [d508, d52336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro335 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52349 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d509 q = 1) (hb : d52350 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d52350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d509, d52350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52351 q = 1) (hb : d53678 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52351, d53678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d52351, d53678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d53679 q = 1) (hb : d55915 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53679, d55915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53679, d55915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d55626 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54879 q = 1) (hb : d55916 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54879, d55916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54879, d55916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54880 q = 1) (hb : d55917 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54880, d55917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54880, d55917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro975 (p : Pattern) (ha : d54886 p = 1) (hb : d55923 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54881 q = 1) (hb : d55918 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54881, d55918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54881, d55918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro974 q ha hb
  have h2 (q : Pattern) (ha : d54882 q = 1) (hb : d55919 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54882, d55919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54882, d55919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54883 q = 1) (hb : d55920 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54883, d55920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54883, d55920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54884 q = 1) (hb : d55921 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54884, d55921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54884, d55921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54885 q = 1) (hb : d55922 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54885, d55922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54885, d55922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54886 q = 1) (hb : d55923 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54886, d55923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54886, d55923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro976 (p : Pattern) (ha : d54889 p = 1) (hb : d55928 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55925 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d800 q = 1) (hb : d52557 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d52557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro340 q ha hb
    | true =>
      simp only [d800, d52557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro341 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52570 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d801 q = 1) (hb : d52571 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d52571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d801, d52571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52572 q = 1) (hb : d53705 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52572, d53705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d52572, d53705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d53706 q = 1) (hb : d55926 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53706, d55926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53706, d55926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d55640 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54888 q = 1) (hb : d55927 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54888, d55927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54888, d55927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54889 q = 1) (hb : d55928 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54889, d55928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54889, d55928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro977 (p : Pattern) (ha : d54895 p = 1) (hb : d55934 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54890 q = 1) (hb : d55929 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54890, d55929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54890, d55929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro976 q ha hb
  have h2 (q : Pattern) (ha : d54891 q = 1) (hb : d55930 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54891, d55930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54891, d55930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54892 q = 1) (hb : d55931 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54892, d55931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54892, d55931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54893 q = 1) (hb : d55932 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54893, d55932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54893, d55932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54894 q = 1) (hb : d55933 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54894, d55933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54894, d55933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54895 q = 1) (hb : d55934 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54895, d55934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54895, d55934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro978 (p : Pattern) (ha : d54899 p = 1) (hb : d55940 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55937 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1179 q = 1) (hb : d52837 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d52837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro346 q ha hb
    | true =>
      simp only [d1179, d52837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro347 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52850 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1180 q = 1) (hb : d52851 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d52851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1180, d52851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52852 q = 1) (hb : d53733 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52852, d53733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d52852, d53733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d53734 q = 1) (hb : d55938 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53734, d55938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53734, d55938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d55655 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54898 q = 1) (hb : d55939 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54898, d55939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54898, d55939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54899 q = 1) (hb : d55940 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54899, d55940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54899, d55940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro979 (p : Pattern) (ha : d54905 p = 1) (hb : d55946 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54900 q = 1) (hb : d55941 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54900, d55941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54900, d55941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro978 q ha hb
  have h2 (q : Pattern) (ha : d54901 q = 1) (hb : d55942 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54901, d55942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54901, d55942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54902 q = 1) (hb : d55943 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54902, d55943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54902, d55943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54903 q = 1) (hb : d55944 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54903, d55944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54903, d55944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54904 q = 1) (hb : d55945 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54904, d55945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54904, d55945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54905 q = 1) (hb : d55946 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54905, d55946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54905, d55946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro980 (p : Pattern) (ha : d54910 p = 1) (hb : d55953 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55950 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1640 q = 1) (hb : d53152 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d53152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro352 q ha hb
    | true =>
      simp only [d1640, d53152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro353 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53165 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1641 q = 1) (hb : d53166 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d53166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1641, d53166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53167 q = 1) (hb : d53762 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53167, d53762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d53167, d53762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d53763 q = 1) (hb : d55951 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53763, d55951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53763, d55951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d55671 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54909 q = 1) (hb : d55952 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54909, d55952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54909, d55952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54910 q = 1) (hb : d55953 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54910, d55953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54910, d55953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro981 (p : Pattern) (ha : d54916 p = 1) (hb : d55959 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54911 q = 1) (hb : d55954 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54911, d55954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54911, d55954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro980 q ha hb
  have h2 (q : Pattern) (ha : d54912 q = 1) (hb : d55955 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54912, d55955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54912, d55955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54913 q = 1) (hb : d55956 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54913, d55956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54913, d55956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54914 q = 1) (hb : d55957 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54914, d55957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54914, d55957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54915 q = 1) (hb : d55958 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54915, d55958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54915, d55958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54916 q = 1) (hb : d55959 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54916, d55959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54916, d55959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro982 (p : Pattern) (ha : d54922 p = 1) (hb : d55967 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55964 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2123 q = 1) (hb : d53469 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d53469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro358 q ha hb
    | true =>
      simp only [d2123, d53469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro359 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53482 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2124 q = 1) (hb : d53483 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d53483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2124, d53483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53484 q = 1) (hb : d53792 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53484, d53792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d53484, d53792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d53793 q = 1) (hb : d55965 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53793, d55965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53793, d55965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d55688 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54921 q = 1) (hb : d55966 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54921, d55966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54921, d55966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54922 q = 1) (hb : d55967 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54922, d55967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54922, d55967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro983 (p : Pattern) (ha : d54928 p = 1) (hb : d55973 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54923 q = 1) (hb : d55968 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54923, d55968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54923, d55968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro982 q ha hb
  have h2 (q : Pattern) (ha : d54924 q = 1) (hb : d55969 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54924, d55969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54924, d55969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54925 q = 1) (hb : d55970 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54925, d55970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54925, d55970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54926 q = 1) (hb : d55971 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54926, d55971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54926, d55971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54927 q = 1) (hb : d55972 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54927, d55972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54927, d55972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54928 q = 1) (hb : d55973 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54928, d55973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54928, d55973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro984 (p : Pattern) (ha : d54934 p = 1) (hb : d55979 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d54887 q = 1) (hb : d55924 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54887, d55924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro973 q ha hb
    | true =>
      simp only [d54887, d55924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro975 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54896 q = 1) (hb : d55935 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54896, d55935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54896, d55935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro977 q ha hb
  have h3 (q : Pattern) (ha : d54897 q = 1) (hb : d55936 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54897, d55936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54897, d55936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54906 q = 1) (hb : d55947 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54906, d55947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54906, d55947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro979 q ha hb
  have h5 (q : Pattern) (ha : d54907 q = 1) (hb : d55948 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54907, d55948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54907, d55948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54908 q = 1) (hb : d55949 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54908, d55949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54908, d55949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54917 q = 1) (hb : d55960 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54917, d55960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54917, d55960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro981 q ha hb
  have h8 (q : Pattern) (ha : d54918 q = 1) (hb : d55961 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54918, d55961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54918, d55961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54919 q = 1) (hb : d55962 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54919, d55962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54919, d55962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54920 q = 1) (hb : d55963 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54920, d55963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54920, d55963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54929 q = 1) (hb : d55974 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54929, d55974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54929, d55974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro983 q ha hb
  have h12 (q : Pattern) (ha : d54930 q = 1) (hb : d55975 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54930, d55975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54930, d55975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54931 q = 1) (hb : d55976 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54931, d55976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54931, d55976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54932 q = 1) (hb : d55977 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54932, d55977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54932, d55977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54933 q = 1) (hb : d55978 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54933, d55978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54933, d55978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54934 q = 1) (hb : d55979 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d54934, d55979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54934, d55979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro985 (p : Pattern) (ha : d54940 p = 1) (hb : d55985 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54935 q = 1) (hb : d55980 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54935, d55980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro984 q ha hb
    | true =>
      simp only [d54935, d55980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54936 q = 1) (hb : d55981 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54936, d55981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54936, d55981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54937 q = 1) (hb : d55982 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54937, d55982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54937, d55982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54938 q = 1) (hb : d55983 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54938, d55983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54938, d55983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54939 q = 1) (hb : d55984 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54939, d55984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54939, d55984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54940 q = 1) (hb : d55985 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d54940, d55985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54940, d55985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro986 (p : Pattern) (ha : d54946 p = 1) (hb : d55991 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54941 q = 1) (hb : d55986 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54941, d55986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro985 q ha hb
    | true =>
      simp only [d54941, d55986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54942 q = 1) (hb : d55987 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54942, d55987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54942, d55987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54943 q = 1) (hb : d55988 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54943, d55988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54943, d55988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54944 q = 1) (hb : d55989 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54944, d55989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54944, d55989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54945 q = 1) (hb : d55990 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54945, d55990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54945, d55990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54946 q = 1) (hb : d55991 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d54946, d55991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54946, d55991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro987 (p : Pattern) (ha : d54952 p = 1) (hb : d55997 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54947 q = 1) (hb : d55992 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54947, d55992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro986 q ha hb
    | true =>
      simp only [d54947, d55992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54948 q = 1) (hb : d55993 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54948, d55993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54948, d55993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54949 q = 1) (hb : d55994 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54949, d55994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54949, d55994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54950 q = 1) (hb : d55995 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54950, d55995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54950, d55995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54951 q = 1) (hb : d55996 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54951, d55996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54951, d55996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54952 q = 1) (hb : d55997 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d54952, d55997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54952, d55997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro988 (p : Pattern) (ha : d54958 p = 1) (hb : d56003 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54953 q = 1) (hb : d55998 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54953, d55998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro987 q ha hb
    | true =>
      simp only [d54953, d55998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54954 q = 1) (hb : d55999 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54954, d55999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54954, d55999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54955 q = 1) (hb : d56000 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54955, d56000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54955, d56000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54956 q = 1) (hb : d56001 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54956, d56001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54956, d56001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54957 q = 1) (hb : d56002 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54957, d56002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54957, d56002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54958 q = 1) (hb : d56003 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d54958, d56003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54958, d56003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro989 (p : Pattern) (ha : d54964 p = 1) (hb : d56009 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54959 q = 1) (hb : d56004 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54959, d56004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro988 q ha hb
    | true =>
      simp only [d54959, d56004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54960 q = 1) (hb : d56005 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54960, d56005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54960, d56005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54961 q = 1) (hb : d56006 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54961, d56006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54961, d56006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54962 q = 1) (hb : d56007 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54962, d56007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54962, d56007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54963 q = 1) (hb : d56008 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54963, d56008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54963, d56008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54964 q = 1) (hb : d56009 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d54964, d56009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54964, d56009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro990 (p : Pattern) (ha : d54970 p = 1) (hb : d56015 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54965 q = 1) (hb : d56010 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54965, d56010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro989 q ha hb
    | true =>
      simp only [d54965, d56010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54966 q = 1) (hb : d56011 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54966, d56011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54966, d56011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54967 q = 1) (hb : d56012 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54967, d56012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54967, d56012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54968 q = 1) (hb : d56013 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54968, d56013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54968, d56013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54969 q = 1) (hb : d56014 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54969, d56014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54969, d56014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54970 q = 1) (hb : d56015 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54970, d56015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54970, d56015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro991 (p : Pattern) (ha : d54976 p = 1) (hb : d56021 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54971 q = 1) (hb : d56016 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54971, d56016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro990 q ha hb
    | true =>
      simp only [d54971, d56016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54972 q = 1) (hb : d56017 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54972, d56017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54972, d56017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54973 q = 1) (hb : d56018 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54973, d56018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54973, d56018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54974 q = 1) (hb : d56019 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54974, d56019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54974, d56019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54975 q = 1) (hb : d56020 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54975, d56020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54975, d56020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54976 q = 1) (hb : d56021 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54976, d56021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54976, d56021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro992 (p : Pattern) (ha : d54865 p = 1) (hb : d56024 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d3016 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d51647 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d51647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro372 q ha hb
    | true =>
      simp only [d112, d51647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro373 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d214 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113 q = 1) (hb : d51648 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d51648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, d51648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51649 q = 1) (hb : d53637 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51649, d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d51649, d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53638 q = 1) (hb : d56022 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, d56022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, d56022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d2528 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54864 q = 1) (hb : d56023 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54864, d56023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54864, d56023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54865 q = 1) (hb : d56024 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54865, d56024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54865, d56024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro993 (p : Pattern) (ha : d54872 p = 1) (hb : d56032 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d3025 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292 q = 1) (hb : d51664 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d51664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro377 q ha hb
    | true =>
      simp only [d292, d51664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro378 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d398 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d293 q = 1) (hb : d51665 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d51665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293, d51665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51666 q = 1) (hb : d53653 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51666, d53653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d51666, d53653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53654 q = 1) (hb : d56030 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, d56030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, d56030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d2540 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54871 q = 1) (hb : d56031 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54871, d56031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54871, d56031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54872 q = 1) (hb : d56032 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54872, d56032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54872, d56032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro994 (p : Pattern) (ha : d54878 p = 1) (hb : d56038 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2524 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54866 q = 1) (hb : d56025 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54866, d56025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54866, d56025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro992 q ha hb
  have h3 (q : Pattern) (ha : d54867 q = 1) (hb : d56026 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54867, d56026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54867, d56026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54868 q = 1) (hb : d56027 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54868, d56027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54868, d56027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54869 q = 1) (hb : d56028 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54869, d56028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54869, d56028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54870 q = 1) (hb : d56029 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54870, d56029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54870, d56029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54873 q = 1) (hb : d56033 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54873, d56033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54873, d56033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro993 q ha hb
  have h8 (q : Pattern) (ha : d54874 q = 1) (hb : d56034 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54874, d56034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54874, d56034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54875 q = 1) (hb : d56035 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54875, d56035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54875, d56035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54876 q = 1) (hb : d56036 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54876, d56036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54876, d56036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54877 q = 1) (hb : d56037 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54877, d56037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54877, d56037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54878 q = 1) (hb : d56038 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54878, d56038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54878, d56038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro995 (p : Pattern) (ha : d54880 p = 1) (hb : d56041 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d3035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d508 q = 1) (hb : d51689 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d51689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro383 q ha hb
    | true =>
      simp only [d508, d51689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro384 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d645 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d509 q = 1) (hb : d51690 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d51690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d509, d51690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51691 q = 1) (hb : d53678 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51691, d53678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d51691, d53678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53679 q = 1) (hb : d56039 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53679, d56039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53679, d56039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d2553 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54879 q = 1) (hb : d56040 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54879, d56040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54879, d56040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54880 q = 1) (hb : d56041 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54880, d56041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54880, d56041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro996 (p : Pattern) (ha : d54886 p = 1) (hb : d56047 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54881 q = 1) (hb : d56042 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54881, d56042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54881, d56042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro995 q ha hb
  have h2 (q : Pattern) (ha : d54882 q = 1) (hb : d56043 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54882, d56043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54882, d56043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54883 q = 1) (hb : d56044 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54883, d56044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54883, d56044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54884 q = 1) (hb : d56045 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54884, d56045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54884, d56045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54885 q = 1) (hb : d56046 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54885, d56046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54885, d56046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54886 q = 1) (hb : d56047 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54886, d56047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54886, d56047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro997 (p : Pattern) (ha : d54889 p = 1) (hb : d56051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d3046 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d800 q = 1) (hb : d51715 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d51715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro389 q ha hb
    | true =>
      simp only [d800, d51715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro390 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d951 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d801 q = 1) (hb : d51716 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d51716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d801, d51716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51717 q = 1) (hb : d53705 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51717, d53705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d51717, d53705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53706 q = 1) (hb : d56049 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53706, d56049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53706, d56049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d2567 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54888 q = 1) (hb : d56050 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54888, d56050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54888, d56050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54889 q = 1) (hb : d56051 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54889, d56051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54889, d56051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro998 (p : Pattern) (ha : d54895 p = 1) (hb : d56057 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54890 q = 1) (hb : d56052 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54890, d56052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54890, d56052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro997 q ha hb
  have h2 (q : Pattern) (ha : d54891 q = 1) (hb : d56053 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54891, d56053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54891, d56053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54892 q = 1) (hb : d56054 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54892, d56054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54892, d56054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54893 q = 1) (hb : d56055 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54893, d56055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54893, d56055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54894 q = 1) (hb : d56056 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54894, d56056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54894, d56056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54895 q = 1) (hb : d56057 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54895, d56057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54895, d56057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro999 (p : Pattern) (ha : d54899 p = 1) (hb : d56062 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d3058 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1179 q = 1) (hb : d51742 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d51742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro395 q ha hb
    | true =>
      simp only [d1179, d51742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro396 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1362 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1180 q = 1) (hb : d51743 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d51743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1180, d51743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51744 q = 1) (hb : d53733 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51744, d53733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d51744, d53733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53734 q = 1) (hb : d56060 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53734, d56060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53734, d56060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d2582 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54898 q = 1) (hb : d56061 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54898, d56061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54898, d56061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54899 q = 1) (hb : d56062 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54899, d56062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54899, d56062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
end NetHack.Soko22Hazard87
