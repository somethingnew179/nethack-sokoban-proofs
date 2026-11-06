import NetHack.Soko22Hazard87.AndIntroBlocks0066
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro16750 (p : Pattern) (ha : d79999 p = 1) (hb : d109809 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71133 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71138 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d109804 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d71112 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d71112 q = 1) (hb : d79994 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16631 q ha hb
    | true =>
      simp only [d79994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d79995 q = 1) (hb : d109805 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79995, d109805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79995, d109805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d79996 q = 1) (hb : d109806 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79996, d109806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79996, d109806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d79997 q = 1) (hb : d109807 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79997, d109807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79997, d109807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d79998 q = 1) (hb : d109808 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79998, d109808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79998, d109808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d79999 q = 1) (hb : d109809 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79999, d109809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79999, d109809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro16751 (p : Pattern) (ha : d80008 p = 1) (hb : d109815 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d71133 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71138 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d109804 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71112 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d71112 q = 1) (hb : d79994 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16631 q ha hb
    | true =>
      simp only [d79994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79995 q = 1) (hb : d109805 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79995, d109805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79995, d109805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d79996 q = 1) (hb : d109806 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79996, d109806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79996, d109806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79997 q = 1) (hb : d109807 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79997, d109807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79997, d109807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d79998 q = 1) (hb : d109808 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79998, d109808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79998, d109808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d71151 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d71154 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d109810 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d71120 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d71120 q = 1) (hb : d80003 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16633 q ha hb
    | true =>
      simp only [d80003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d80004 q = 1) (hb : d109811 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80004, d109811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d80004, d109811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d80005 q = 1) (hb : d109812 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80005, d109812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d80005, d109812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h17 (q : Pattern) (ha : d80006 q = 1) (hb : d109813 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80006, d109813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d80006, d109813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d80007 q = 1) (hb : d109814 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80007, d109814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d80007, d109814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d80008 q = 1) (hb : d109815 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80008, d109815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d80008, d109815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro16752 (p : Pattern) (ha : d80431 p = 1) (hb : d109824 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d109810 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71120 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71120 q = 1) (hb : d80003 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16633 q ha hb
    | true =>
      simp only [d80003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d80004 q = 1) (hb : d109811 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80004, d109811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80004, d109811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d80005 q = 1) (hb : d109812 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80005, d109812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80005, d109812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d80006 q = 1) (hb : d109822 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80006, d109822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80006, d109822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80007 q = 1) (hb : d109823 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80007, d109823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80007, d109823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d80431 q = 1) (hb : d109824 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80431, d109824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80431, d109824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16753 (p : Pattern) (ha : d71179 p = 1) (hb : d80073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52920 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1431 q = 1) (hb : d52919 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1431, d52919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro169 q ha hb
    | true =>
      simp only [d1431, d52919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1432 q = 1) (hb : d52920 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, d52920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1432, d52920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52920 q = 1) (hb : d80070 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d80070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d71177 q = 1) (hb : d80071 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d71177, d80071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71177, d80071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d71178 q = 1) (hb : d80072 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d71178, d80072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71178, d80072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d71179 q = 1) (hb : d80073 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d71179, d80073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71179, d80073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro16754 (p : Pattern) (ha : d80441 p = 1) (hb : d109837 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d109832 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71179 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71179 q = 1) (hb : d80074 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16753 q ha hb
    | true =>
      simp only [d80074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d80437 q = 1) (hb : d109833 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80437, d109833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80437, d109833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d80438 q = 1) (hb : d109834 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80438, d109834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80438, d109834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d80439 q = 1) (hb : d109835 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80439, d109835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80439, d109835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80440 q = 1) (hb : d109836 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80440, d109836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80440, d109836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d80441 q = 1) (hb : d109837 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80441, d109837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80441, d109837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16755 (p : Pattern) (ha : d80447 p = 1) (hb : d109843 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d71128 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80009 q = 1) (hb : d109816 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80009, d109816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16750 q ha hb
    | true =>
      simp only [d80009, d109816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16751 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d109818 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d80010 q = 1) (hb : d109819 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80010, d109819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80010, d109819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d80429 q = 1) (hb : d109820 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80429, d109820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80429, d109820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80430 q = 1) (hb : d109821 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80430, d109821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80430, d109821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80432 q = 1) (hb : d109825 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80432, d109825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80432, d109825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16752 q ha hb
  have h8 (q : Pattern) (ha : d80433 q = 1) (hb : d109826 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80433, d109826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d80433, d109826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d80434 q = 1) (hb : d109827 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80434, d109827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d80434, d109827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d80435 q = 1) (hb : d109828 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80435, d109828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d80435, d109828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d80436 q = 1) (hb : d109829 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d80436, d109829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d80436, d109829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d80442 q = 1) (hb : d109838 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80442, d109838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80442, d109838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16754 q ha hb
  have h13 (q : Pattern) (ha : d80443 q = 1) (hb : d109839 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80443, d109839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d80443, d109839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d80444 q = 1) (hb : d109840 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80444, d109840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d80444, d109840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d80445 q = 1) (hb : d109841 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80445, d109841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d80445, d109841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d80446 q = 1) (hb : d109842 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d80446, d109842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d80446, d109842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d80447 q = 1) (hb : d109843 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d80447, d109843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d80447, d109843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro16756 (p : Pattern) (ha : d80453 p = 1) (hb : d109849 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80448 q = 1) (hb : d109844 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d80448, d109844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80448, d109844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16755 q ha hb
  have h2 (q : Pattern) (ha : d80449 q = 1) (hb : d109845 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d80449, d109845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80449, d109845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d80450 q = 1) (hb : d109846 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d80450, d109846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80450, d109846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d80451 q = 1) (hb : d109847 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d80451, d109847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80451, d109847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d80452 q = 1) (hb : d109848 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d80452, d109848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80452, d109848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80453 q = 1) (hb : d109849 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d80453, d109849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80453, d109849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16757 (p : Pattern) (ha : d80104 p = 1) (hb : d109860 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71224 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71229 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d109855 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d71203 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d71203 q = 1) (hb : d80099 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16649 q ha hb
    | true =>
      simp only [d80099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d80100 q = 1) (hb : d109856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80100, d109856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80100, d109856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d80101 q = 1) (hb : d109857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80101, d109857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d80101, d109857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d80102 q = 1) (hb : d109858 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80102, d109858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80102, d109858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d80103 q = 1) (hb : d109859 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80103, d109859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80103, d109859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d80104 q = 1) (hb : d109860 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80104, d109860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80104, d109860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro16758 (p : Pattern) (ha : d80113 p = 1) (hb : d109866 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d71224 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71229 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d109855 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71203 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d71203 q = 1) (hb : d80099 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16649 q ha hb
    | true =>
      simp only [d80099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d80100 q = 1) (hb : d109856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80100, d109856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80100, d109856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d80101 q = 1) (hb : d109857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80101, d109857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d80101, d109857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d80102 q = 1) (hb : d109858 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80102, d109858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80102, d109858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d80103 q = 1) (hb : d109859 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80103, d109859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80103, d109859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d71242 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d71245 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d109861 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d71211 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d71211 q = 1) (hb : d80108 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16651 q ha hb
    | true =>
      simp only [d80108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d80109 q = 1) (hb : d109862 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80109, d109862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d80109, d109862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d80110 q = 1) (hb : d109863 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80110, d109863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d80110, d109863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h17 (q : Pattern) (ha : d80111 q = 1) (hb : d109864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80111, d109864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d80111, d109864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d80112 q = 1) (hb : d109865 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80112, d109865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d80112, d109865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d80113 q = 1) (hb : d109866 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80113, d109866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d80113, d109866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro16759 (p : Pattern) (ha : d80459 p = 1) (hb : d109875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d109861 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71211 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71211 q = 1) (hb : d80108 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16651 q ha hb
    | true =>
      simp only [d80108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d80109 q = 1) (hb : d109862 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80109, d109862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80109, d109862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d80110 q = 1) (hb : d109863 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80110, d109863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80110, d109863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d80111 q = 1) (hb : d109873 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80111, d109873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80111, d109873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80112 q = 1) (hb : d109874 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80112, d109874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80112, d109874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d80459 q = 1) (hb : d109875 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80459, d109875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80459, d109875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16760 (p : Pattern) (ha : d71270 p = 1) (hb : d80178 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53235 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1908 q = 1) (hb : d53234 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, d53234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro227 q ha hb
    | true =>
      simp only [d1908, d53234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1909 q = 1) (hb : d53235 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, d53235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1909, d53235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53235 q = 1) (hb : d80175 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d80175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d71268 q = 1) (hb : d80176 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d71268, d80176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71268, d80176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d71269 q = 1) (hb : d80177 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d71269, d80177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71269, d80177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d71270 q = 1) (hb : d80178 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d71270, d80178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71270, d80178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro16761 (p : Pattern) (ha : d80469 p = 1) (hb : d109888 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d109883 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71270 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71270 q = 1) (hb : d80179 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16760 q ha hb
    | true =>
      simp only [d80179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d80465 q = 1) (hb : d109884 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80465, d109884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80465, d109884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d80466 q = 1) (hb : d109885 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80466, d109885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80466, d109885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d80467 q = 1) (hb : d109886 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80467, d109886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80467, d109886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80468 q = 1) (hb : d109887 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80468, d109887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80468, d109887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d80469 q = 1) (hb : d109888 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80469, d109888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80469, d109888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16762 (p : Pattern) (ha : d80475 p = 1) (hb : d109894 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d71219 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80114 q = 1) (hb : d109867 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80114, d109867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16757 q ha hb
    | true =>
      simp only [d80114, d109867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16758 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d109869 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d80115 q = 1) (hb : d109870 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80115, d109870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80115, d109870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d80457 q = 1) (hb : d109871 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80457, d109871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80457, d109871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80458 q = 1) (hb : d109872 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80458, d109872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80458, d109872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80460 q = 1) (hb : d109876 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80460, d109876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80460, d109876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16759 q ha hb
  have h8 (q : Pattern) (ha : d80461 q = 1) (hb : d109877 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80461, d109877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d80461, d109877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d80462 q = 1) (hb : d109878 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80462, d109878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d80462, d109878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d80463 q = 1) (hb : d109879 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80463, d109879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d80463, d109879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d80464 q = 1) (hb : d109880 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d80464, d109880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d80464, d109880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d80470 q = 1) (hb : d109889 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80470, d109889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80470, d109889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16761 q ha hb
  have h13 (q : Pattern) (ha : d80471 q = 1) (hb : d109890 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80471, d109890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d80471, d109890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d80472 q = 1) (hb : d109891 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80472, d109891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d80472, d109891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d80473 q = 1) (hb : d109892 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80473, d109892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d80473, d109892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d80474 q = 1) (hb : d109893 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d80474, d109893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d80474, d109893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d80475 q = 1) (hb : d109894 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d80475, d109894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d80475, d109894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro16763 (p : Pattern) (ha : d80481 p = 1) (hb : d109900 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80476 q = 1) (hb : d109895 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d80476, d109895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80476, d109895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16762 q ha hb
  have h2 (q : Pattern) (ha : d80477 q = 1) (hb : d109896 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d80477, d109896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80477, d109896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d80478 q = 1) (hb : d109897 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d80478, d109897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80478, d109897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d80479 q = 1) (hb : d109898 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d80479, d109898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80479, d109898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d80480 q = 1) (hb : d109899 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d80480, d109899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80480, d109899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80481 q = 1) (hb : d109900 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d80481, d109900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80481, d109900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16764 (p : Pattern) (ha : d80210 p = 1) (hb : d109912 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71316 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71321 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d109907 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d71295 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d71295 q = 1) (hb : d80205 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16667 q ha hb
    | true =>
      simp only [d80205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d80206 q = 1) (hb : d109908 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80206, d109908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80206, d109908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d80207 q = 1) (hb : d109909 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80207, d109909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d80207, d109909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d80208 q = 1) (hb : d109910 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80208, d109910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80208, d109910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d80209 q = 1) (hb : d109911 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80209, d109911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80209, d109911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d80210 q = 1) (hb : d109912 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80210, d109912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80210, d109912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro16765 (p : Pattern) (ha : d80219 p = 1) (hb : d109918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d71316 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71321 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d109907 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71295 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d71295 q = 1) (hb : d80205 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16667 q ha hb
    | true =>
      simp only [d80205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d80206 q = 1) (hb : d109908 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80206, d109908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80206, d109908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d80207 q = 1) (hb : d109909 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80207, d109909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d80207, d109909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d80208 q = 1) (hb : d109910 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80208, d109910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80208, d109910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d80209 q = 1) (hb : d109911 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80209, d109911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80209, d109911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d71334 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d71337 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d109913 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d71303 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d71303 q = 1) (hb : d80214 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16669 q ha hb
    | true =>
      simp only [d80214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d80215 q = 1) (hb : d109914 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80215, d109914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d80215, d109914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d80216 q = 1) (hb : d109915 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80216, d109915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d80216, d109915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h17 (q : Pattern) (ha : d80217 q = 1) (hb : d109916 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80217, d109916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d80217, d109916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d80218 q = 1) (hb : d109917 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80218, d109917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d80218, d109917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d80219 q = 1) (hb : d109918 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80219, d109918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d80219, d109918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro16766 (p : Pattern) (ha : d80488 p = 1) (hb : d109927 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d109913 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71303 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71303 q = 1) (hb : d80214 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16669 q ha hb
    | true =>
      simp only [d80214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d80215 q = 1) (hb : d109914 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80215, d109914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80215, d109914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d80216 q = 1) (hb : d109915 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80216, d109915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80216, d109915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d80217 q = 1) (hb : d109925 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80217, d109925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80217, d109925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80218 q = 1) (hb : d109926 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80218, d109926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80218, d109926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d80488 q = 1) (hb : d109927 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80488, d109927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80488, d109927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16767 (p : Pattern) (ha : d71362 p = 1) (hb : d80284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53552 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2386 q = 1) (hb : d53551 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2386, d53551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro286 q ha hb
    | true =>
      simp only [d2386, d53551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2387 q = 1) (hb : d53552 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2387, d53552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2387, d53552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53552 q = 1) (hb : d80281 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d80281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d71360 q = 1) (hb : d80282 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d71360, d80282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71360, d80282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d71361 q = 1) (hb : d80283 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d71361, d80283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71361, d80283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d71362 q = 1) (hb : d80284 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d71362, d80284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71362, d80284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro16768 (p : Pattern) (ha : d80498 p = 1) (hb : d109940 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d109935 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71362 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71362 q = 1) (hb : d80285 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16767 q ha hb
    | true =>
      simp only [d80285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d80494 q = 1) (hb : d109936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80494, d109936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80494, d109936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d80495 q = 1) (hb : d109937 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80495, d109937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80495, d109937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d80496 q = 1) (hb : d109938 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80496, d109938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80496, d109938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80497 q = 1) (hb : d109939 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80497, d109939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80497, d109939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d80498 q = 1) (hb : d109940 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80498, d109940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80498, d109940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16769 (p : Pattern) (ha : d80504 p = 1) (hb : d109946 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d71311 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80220 q = 1) (hb : d109919 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80220, d109919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16764 q ha hb
    | true =>
      simp only [d80220, d109919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16765 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d109921 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d80221 q = 1) (hb : d109922 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80221, d109922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80221, d109922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d80486 q = 1) (hb : d109923 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80486, d109923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80486, d109923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80487 q = 1) (hb : d109924 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80487, d109924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80487, d109924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80489 q = 1) (hb : d109928 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80489, d109928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80489, d109928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16766 q ha hb
  have h8 (q : Pattern) (ha : d80490 q = 1) (hb : d109929 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80490, d109929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d80490, d109929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d80491 q = 1) (hb : d109930 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80491, d109930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d80491, d109930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d80492 q = 1) (hb : d109931 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80492, d109931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d80492, d109931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d80493 q = 1) (hb : d109932 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d80493, d109932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d80493, d109932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d80499 q = 1) (hb : d109941 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80499, d109941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80499, d109941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16768 q ha hb
  have h13 (q : Pattern) (ha : d80500 q = 1) (hb : d109942 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80500, d109942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d80500, d109942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d80501 q = 1) (hb : d109943 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80501, d109943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d80501, d109943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d80502 q = 1) (hb : d109944 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80502, d109944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d80502, d109944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d80503 q = 1) (hb : d109945 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d80503, d109945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d80503, d109945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d80504 q = 1) (hb : d109946 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d80504, d109946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d80504, d109946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro16770 (p : Pattern) (ha : d80510 p = 1) (hb : d109952 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80505 q = 1) (hb : d109947 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d80505, d109947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80505, d109947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16769 q ha hb
  have h2 (q : Pattern) (ha : d80506 q = 1) (hb : d109948 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d80506, d109948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80506, d109948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d80507 q = 1) (hb : d109949 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d80507, d109949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80507, d109949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d80508 q = 1) (hb : d109950 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d80508, d109950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80508, d109950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d80509 q = 1) (hb : d109951 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d80509, d109951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80509, d109951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80510 q = 1) (hb : d109952 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d80510, d109952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80510, d109952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16771 (p : Pattern) (ha : d80516 p = 1) (hb : d109958 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d80401 q = 1) (hb : d109751 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d80401, d109751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16735 q ha hb
    | true =>
      simp only [d80401, d109751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16742 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d80427 q = 1) (hb : d109800 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d80427, d109800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80427, d109800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16749 q ha hb
  have h3 (q : Pattern) (ha : d80428 q = 1) (hb : d109801 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d80428, d109801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80428, d109801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d80454 q = 1) (hb : d109850 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d80454, d109850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80454, d109850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16756 q ha hb
  have h5 (q : Pattern) (ha : d80455 q = 1) (hb : d109851 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d80455, d109851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80455, d109851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80456 q = 1) (hb : d109852 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d80456, d109852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80456, d109852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80482 q = 1) (hb : d109901 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d80482, d109901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80482, d109901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16763 q ha hb
  have h8 (q : Pattern) (ha : d80483 q = 1) (hb : d109902 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d80483, d109902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80483, d109902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d80484 q = 1) (hb : d109903 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d80484, d109903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80484, d109903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d80485 q = 1) (hb : d109904 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d80485, d109904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d80485, d109904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d80511 q = 1) (hb : d109953 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d80511, d109953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80511, d109953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16770 q ha hb
  have h12 (q : Pattern) (ha : d80512 q = 1) (hb : d109954 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d80512, d109954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80512, d109954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d80513 q = 1) (hb : d109955 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d80513, d109955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80513, d109955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d80514 q = 1) (hb : d109956 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d80514, d109956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80514, d109956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d80515 q = 1) (hb : d109957 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d80515, d109957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d80515, d109957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d80516 q = 1) (hb : d109958 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d80516, d109958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d80516, d109958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro16772 (p : Pattern) (ha : d80522 p = 1) (hb : d109964 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80517 q = 1) (hb : d109959 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d80517, d109959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16771 q ha hb
    | true =>
      simp only [d80517, d109959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d80518 q = 1) (hb : d109960 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d80518, d109960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80518, d109960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d80519 q = 1) (hb : d109961 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d80519, d109961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80519, d109961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d80520 q = 1) (hb : d109962 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d80520, d109962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80520, d109962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d80521 q = 1) (hb : d109963 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d80521, d109963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80521, d109963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d80522 q = 1) (hb : d109964 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d80522, d109964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d80522, d109964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16773 (p : Pattern) (ha : d80528 p = 1) (hb : d109970 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80523 q = 1) (hb : d109965 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d80523, d109965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16772 q ha hb
    | true =>
      simp only [d80523, d109965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d80524 q = 1) (hb : d109966 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d80524, d109966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80524, d109966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d80525 q = 1) (hb : d109967 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d80525, d109967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80525, d109967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d80526 q = 1) (hb : d109968 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d80526, d109968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80526, d109968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d80527 q = 1) (hb : d109969 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d80527, d109969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80527, d109969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d80528 q = 1) (hb : d109970 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d80528, d109970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d80528, d109970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16774 (p : Pattern) (ha : d80534 p = 1) (hb : d109976 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80529 q = 1) (hb : d109971 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d80529, d109971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16773 q ha hb
    | true =>
      simp only [d80529, d109971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d80530 q = 1) (hb : d109972 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d80530, d109972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80530, d109972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d80531 q = 1) (hb : d109973 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d80531, d109973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80531, d109973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d80532 q = 1) (hb : d109974 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d80532, d109974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80532, d109974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d80533 q = 1) (hb : d109975 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d80533, d109975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80533, d109975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d80534 q = 1) (hb : d109976 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d80534, d109976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d80534, d109976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16775 (p : Pattern) (ha : d80540 p = 1) (hb : d109982 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80535 q = 1) (hb : d109977 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d80535, d109977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16774 q ha hb
    | true =>
      simp only [d80535, d109977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d80536 q = 1) (hb : d109978 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d80536, d109978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80536, d109978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d80537 q = 1) (hb : d109979 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d80537, d109979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80537, d109979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d80538 q = 1) (hb : d109980 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d80538, d109980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80538, d109980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d80539 q = 1) (hb : d109981 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d80539, d109981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80539, d109981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d80540 q = 1) (hb : d109982 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d80540, d109982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d80540, d109982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16776 (p : Pattern) (ha : d80546 p = 1) (hb : d109988 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80541 q = 1) (hb : d109983 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d80541, d109983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16775 q ha hb
    | true =>
      simp only [d80541, d109983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d80542 q = 1) (hb : d109984 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d80542, d109984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80542, d109984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d80543 q = 1) (hb : d109985 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d80543, d109985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80543, d109985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d80544 q = 1) (hb : d109986 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d80544, d109986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80544, d109986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d80545 q = 1) (hb : d109987 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d80545, d109987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80545, d109987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d80546 q = 1) (hb : d109988 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d80546, d109988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d80546, d109988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16777 (p : Pattern) (ha : d80552 p = 1) (hb : d109994 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80547 q = 1) (hb : d109989 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d80547, d109989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16776 q ha hb
    | true =>
      simp only [d80547, d109989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d80548 q = 1) (hb : d109990 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d80548, d109990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80548, d109990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d80549 q = 1) (hb : d109991 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d80549, d109991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80549, d109991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d80550 q = 1) (hb : d109992 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d80550, d109992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80550, d109992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d80551 q = 1) (hb : d109993 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d80551, d109993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80551, d109993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d80552 q = 1) (hb : d109994 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d80552, d109994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d80552, d109994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16778 (p : Pattern) (ha : d80558 p = 1) (hb : d110000 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80553 q = 1) (hb : d109995 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d80553, d109995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16777 q ha hb
    | true =>
      simp only [d80553, d109995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d80554 q = 1) (hb : d109996 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d80554, d109996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80554, d109996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d80555 q = 1) (hb : d109997 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d80555, d109997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80555, d109997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d80556 q = 1) (hb : d109998 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d80556, d109998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80556, d109998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d80557 q = 1) (hb : d109999 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d80557, d109999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80557, d109999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d80558 q = 1) (hb : d110000 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d80558, d110000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d80558, d110000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16779 (p : Pattern) (ha : d79700 p = 1) (hb : d110290 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70211 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d70216 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70219 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d79652 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d72175 q = 1) (hb : d79696 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d72175, d79696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d72175, d79696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79697 q = 1) (hb : d110287 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79697, d110287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d79697, d110287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d79698 q = 1) (hb : d110288 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79698, d110288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79698, d110288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79699 q = 1) (hb : d110289 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79699, d110289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79699, d110289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d79700 q = 1) (hb : d110290 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79700, d110290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79700, d110290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro16780 (p : Pattern) (ha : d79707 p = 1) (hb : d110294 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70211 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70216 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d70219 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79652 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d72175 q = 1) (hb : d79696 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d72175, d79696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d72175, d79696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d79697 q = 1) (hb : d110287 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79697, d110287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d79697, d110287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79698 q = 1) (hb : d110288 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79698, d110288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79698, d110288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79699 q = 1) (hb : d110289 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79699, d110289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79699, d110289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d70231 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d70234 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d70235 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d79659 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d72180 q = 1) (hb : d79703 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d72180, d79703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d72180, d79703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d79704 q = 1) (hb : d110291 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79704, d110291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d79704, d110291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h15 (q : Pattern) (ha : d79705 q = 1) (hb : d110292 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79705, d110292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d79705, d110292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d79706 q = 1) (hb : d110293 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79706, d110293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d79706, d110293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d79707 q = 1) (hb : d110294 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79707, d110294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d79707, d110294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro16781 (p : Pattern) (ha : d80353 p = 1) (hb : d110301 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70235 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d79659 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d72180 q = 1) (hb : d79703 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d72180, d79703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d72180, d79703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79704 q = 1) (hb : d110291 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79704, d110291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d79704, d110291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d79705 q = 1) (hb : d110299 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79705, d110299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79705, d110299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79706 q = 1) (hb : d110300 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79706, d110300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79706, d110300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80353 q = 1) (hb : d110301 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80353, d110301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80353, d110301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16782 (p : Pattern) (ha : d80363 p = 1) (hb : d110310 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70256 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d79679 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d72197 q = 1) (hb : d80359 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d72197, d80359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d72197, d80359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d80360 q = 1) (hb : d110307 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80360, d110307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d80360, d110307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d80361 q = 1) (hb : d110308 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80361, d110308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80361, d110308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80362 q = 1) (hb : d110309 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80362, d110309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80362, d110309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80363 q = 1) (hb : d110310 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80363, d110310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80363, d110310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16783 (p : Pattern) (ha : d80369 p = 1) (hb : d110316 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70206 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79708 q = 1) (hb : d110295 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79708, d110295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16779 q ha hb
    | true =>
      simp only [d79708, d110295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16780 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d109339 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d79709 q = 1) (hb : d110296 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79709, d110296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79709, d110296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d80351 q = 1) (hb : d110297 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80351, d110297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80351, d110297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80352 q = 1) (hb : d110298 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80352, d110298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80352, d110298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80354 q = 1) (hb : d110302 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80354, d110302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80354, d110302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16781 q ha hb
  have h8 (q : Pattern) (ha : d80355 q = 1) (hb : d110303 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80355, d110303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d80355, d110303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d80356 q = 1) (hb : d110304 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80356, d110304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d80356, d110304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d80357 q = 1) (hb : d110305 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80357, d110305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d80357, d110305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d80358 q = 1) (hb : d110306 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d80358, d110306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d80358, d110306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d80364 q = 1) (hb : d110311 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80364, d110311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80364, d110311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16782 q ha hb
  have h13 (q : Pattern) (ha : d80365 q = 1) (hb : d110312 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80365, d110312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d80365, d110312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d80366 q = 1) (hb : d110313 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80366, d110313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d80366, d110313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d80367 q = 1) (hb : d110314 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80367, d110314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d80367, d110314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d80368 q = 1) (hb : d110315 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d80368, d110315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d80368, d110315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d80369 q = 1) (hb : d110316 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d80369, d110316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d80369, d110316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro16784 (p : Pattern) (ha : d80375 p = 1) (hb : d110322 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d80370 q = 1) (hb : d110317 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d80370, d110317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80370, d110317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16783 q ha hb
  have h3 (q : Pattern) (ha : d80371 q = 1) (hb : d110318 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d80371, d110318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80371, d110318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d80372 q = 1) (hb : d110319 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d80372, d110319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80372, d110319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d80373 q = 1) (hb : d110320 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d80373, d110320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80373, d110320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80374 q = 1) (hb : d110321 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d80374, d110321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80374, d110321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80375 q = 1) (hb : d110322 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d80375, d110322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80375, d110322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16785 (p : Pattern) (ha : d79792 p = 1) (hb : d110327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70300 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d70305 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d109369 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d79787 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d79788 q = 1) (hb : d110323 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79788, d110323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79788, d110323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d79789 q = 1) (hb : d110324 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79789, d110324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79789, d110324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d79790 q = 1) (hb : d110325 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79790, d110325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79790, d110325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79791 q = 1) (hb : d110326 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79791, d110326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79791, d110326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d79792 q = 1) (hb : d110327 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79792, d110327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79792, d110327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro16786 (p : Pattern) (ha : d79801 p = 1) (hb : d110332 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70305 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d109369 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79787 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79788 q = 1) (hb : d110323 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79788, d110323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79788, d110323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d79789 q = 1) (hb : d110324 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79789, d110324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79789, d110324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79790 q = 1) (hb : d110325 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79790, d110325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79790, d110325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79791 q = 1) (hb : d110326 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79791, d110326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79791, d110326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d70321 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d70324 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d109375 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d79796 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d79797 q = 1) (hb : d110328 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79797, d110328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d79797, d110328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d79798 q = 1) (hb : d110329 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79798, d110329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d79798, d110329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h15 (q : Pattern) (ha : d79799 q = 1) (hb : d110330 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79799, d110330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d79799, d110330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d79800 q = 1) (hb : d110331 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79800, d110331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d79800, d110331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d79801 q = 1) (hb : d110332 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79801, d110332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d79801, d110332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro16787 (p : Pattern) (ha : d80378 p = 1) (hb : d110339 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d109375 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d79796 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d79797 q = 1) (hb : d110328 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79797, d110328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79797, d110328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d79798 q = 1) (hb : d110329 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79798, d110329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79798, d110329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d79799 q = 1) (hb : d110337 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79799, d110337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79799, d110337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79800 q = 1) (hb : d110338 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79800, d110338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79800, d110338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80378 q = 1) (hb : d110339 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80378, d110339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80378, d110339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16788 (p : Pattern) (ha : d80388 p = 1) (hb : d110349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d109397 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d79867 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d80384 q = 1) (hb : d110345 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80384, d110345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80384, d110345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d80385 q = 1) (hb : d110346 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80385, d110346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80385, d110346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d80386 q = 1) (hb : d110347 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80386, d110347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80386, d110347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80387 q = 1) (hb : d110348 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80387, d110348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80387, d110348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80388 q = 1) (hb : d110349 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80388, d110349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80388, d110349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16789 (p : Pattern) (ha : d80394 p = 1) (hb : d110355 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70295 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79802 q = 1) (hb : d110333 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79802, d110333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16785 q ha hb
    | true =>
      simp only [d79802, d110333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16786 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d109383 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d79803 q = 1) (hb : d110334 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79803, d110334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79803, d110334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d80376 q = 1) (hb : d110335 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80376, d110335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80376, d110335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80377 q = 1) (hb : d110336 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80377, d110336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80377, d110336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80379 q = 1) (hb : d110340 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80379, d110340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80379, d110340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16787 q ha hb
  have h8 (q : Pattern) (ha : d80380 q = 1) (hb : d110341 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80380, d110341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d80380, d110341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d80381 q = 1) (hb : d110342 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80381, d110342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d80381, d110342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d80382 q = 1) (hb : d110343 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80382, d110343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d80382, d110343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d80383 q = 1) (hb : d110344 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d80383, d110344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d80383, d110344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d80389 q = 1) (hb : d110350 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80389, d110350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80389, d110350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16788 q ha hb
  have h13 (q : Pattern) (ha : d80390 q = 1) (hb : d110351 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80390, d110351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d80390, d110351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d80391 q = 1) (hb : d110352 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80391, d110352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d80391, d110352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d80392 q = 1) (hb : d110353 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80392, d110353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d80392, d110353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d80393 q = 1) (hb : d110354 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d80393, d110354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d80393, d110354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d80394 q = 1) (hb : d110355 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d80394, d110355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d80394, d110355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro16790 (p : Pattern) (ha : d80400 p = 1) (hb : d110361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80395 q = 1) (hb : d110356 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d80395, d110356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80395, d110356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16789 q ha hb
  have h2 (q : Pattern) (ha : d80396 q = 1) (hb : d110357 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d80396, d110357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80396, d110357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d80397 q = 1) (hb : d110358 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d80397, d110358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80397, d110358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d80398 q = 1) (hb : d110359 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d80398, d110359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80398, d110359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d80399 q = 1) (hb : d110360 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d80399, d110360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80399, d110360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80400 q = 1) (hb : d110361 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d80400, d110361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80400, d110361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16791 (p : Pattern) (ha : d79895 p = 1) (hb : d110367 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70396 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d70401 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d109418 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d79890 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d79891 q = 1) (hb : d110363 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79891, d110363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79891, d110363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d79892 q = 1) (hb : d110364 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79892, d110364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79892, d110364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d79893 q = 1) (hb : d110365 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79893, d110365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79893, d110365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79894 q = 1) (hb : d110366 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79894, d110366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79894, d110366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d79895 q = 1) (hb : d110367 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79895, d110367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79895, d110367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro16792 (p : Pattern) (ha : d79904 p = 1) (hb : d110372 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70396 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70401 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d109418 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79890 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79891 q = 1) (hb : d110363 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79891, d110363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79891, d110363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d79892 q = 1) (hb : d110364 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79892, d110364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79892, d110364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79893 q = 1) (hb : d110365 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79893, d110365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79893, d110365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79894 q = 1) (hb : d110366 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79894, d110366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79894, d110366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d70417 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d70420 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d109424 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d79899 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d79900 q = 1) (hb : d110368 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79900, d110368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d79900, d110368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d79901 q = 1) (hb : d110369 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79901, d110369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d79901, d110369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h15 (q : Pattern) (ha : d79902 q = 1) (hb : d110370 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79902, d110370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d79902, d110370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d79903 q = 1) (hb : d110371 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79903, d110371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d79903, d110371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d79904 q = 1) (hb : d110372 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79904, d110372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d79904, d110372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro16793 (p : Pattern) (ha : d80404 p = 1) (hb : d110379 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d109424 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d79899 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d79900 q = 1) (hb : d110368 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79900, d110368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79900, d110368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d79901 q = 1) (hb : d110369 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79901, d110369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79901, d110369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d79902 q = 1) (hb : d110377 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79902, d110377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79902, d110377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79903 q = 1) (hb : d110378 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79903, d110378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79903, d110378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80404 q = 1) (hb : d110379 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80404, d110379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80404, d110379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16794 (p : Pattern) (ha : d80414 p = 1) (hb : d110389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d109446 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d79970 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d80410 q = 1) (hb : d110385 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80410, d110385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80410, d110385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d80411 q = 1) (hb : d110386 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80411, d110386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80411, d110386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d80412 q = 1) (hb : d110387 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80412, d110387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80412, d110387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80413 q = 1) (hb : d110388 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80413, d110388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80413, d110388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80414 q = 1) (hb : d110389 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80414, d110389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80414, d110389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16795 (p : Pattern) (ha : d80420 p = 1) (hb : d110395 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70391 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79905 q = 1) (hb : d110373 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79905, d110373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16791 q ha hb
    | true =>
      simp only [d79905, d110373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16792 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d109432 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d79906 q = 1) (hb : d110374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79906, d110374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79906, d110374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d80402 q = 1) (hb : d110375 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80402, d110375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80402, d110375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80403 q = 1) (hb : d110376 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80403, d110376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80403, d110376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80405 q = 1) (hb : d110380 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80405, d110380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80405, d110380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16793 q ha hb
  have h8 (q : Pattern) (ha : d80406 q = 1) (hb : d110381 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80406, d110381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d80406, d110381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d80407 q = 1) (hb : d110382 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80407, d110382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d80407, d110382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d80408 q = 1) (hb : d110383 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80408, d110383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d80408, d110383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d80409 q = 1) (hb : d110384 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d80409, d110384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d80409, d110384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d80415 q = 1) (hb : d110390 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80415, d110390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80415, d110390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16794 q ha hb
  have h13 (q : Pattern) (ha : d80416 q = 1) (hb : d110391 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80416, d110391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d80416, d110391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d80417 q = 1) (hb : d110392 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80417, d110392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d80417, d110392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d80418 q = 1) (hb : d110393 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80418, d110393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d80418, d110393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d80419 q = 1) (hb : d110394 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d80419, d110394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d80419, d110394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d80420 q = 1) (hb : d110395 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d80420, d110395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d80420, d110395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro16796 (p : Pattern) (ha : d80426 p = 1) (hb : d110401 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80421 q = 1) (hb : d110396 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d80421, d110396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80421, d110396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16795 q ha hb
  have h2 (q : Pattern) (ha : d80422 q = 1) (hb : d110397 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d80422, d110397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80422, d110397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d80423 q = 1) (hb : d110398 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d80423, d110398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80423, d110398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d80424 q = 1) (hb : d110399 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d80424, d110399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80424, d110399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d80425 q = 1) (hb : d110400 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d80425, d110400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80425, d110400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80426 q = 1) (hb : d110401 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d80426, d110401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80426, d110401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16797 (p : Pattern) (ha : d79999 p = 1) (hb : d110408 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70493 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d70498 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d109468 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d79994 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d79995 q = 1) (hb : d110404 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79995, d110404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79995, d110404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d79996 q = 1) (hb : d110405 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79996, d110405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79996, d110405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d79997 q = 1) (hb : d110406 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79997, d110406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79997, d110406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79998 q = 1) (hb : d110407 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79998, d110407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79998, d110407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d79999 q = 1) (hb : d110408 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79999, d110408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79999, d110408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro16798 (p : Pattern) (ha : d80008 p = 1) (hb : d110413 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70498 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d109468 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79994 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79995 q = 1) (hb : d110404 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79995, d110404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79995, d110404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d79996 q = 1) (hb : d110405 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79996, d110405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79996, d110405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79997 q = 1) (hb : d110406 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79997, d110406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79997, d110406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79998 q = 1) (hb : d110407 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79998, d110407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79998, d110407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d70514 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d70517 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d109474 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d80003 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d80004 q = 1) (hb : d110409 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80004, d110409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d80004, d110409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d80005 q = 1) (hb : d110410 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80005, d110410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d80005, d110410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h15 (q : Pattern) (ha : d80006 q = 1) (hb : d110411 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80006, d110411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d80006, d110411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d80007 q = 1) (hb : d110412 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80007, d110412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d80007, d110412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d80008 q = 1) (hb : d110413 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80008, d110413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d80008, d110413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro16799 (p : Pattern) (ha : d80431 p = 1) (hb : d110420 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d109474 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d80003 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d80004 q = 1) (hb : d110409 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80004, d110409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80004, d110409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d80005 q = 1) (hb : d110410 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80005, d110410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80005, d110410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d80006 q = 1) (hb : d110418 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80006, d110418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80006, d110418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80007 q = 1) (hb : d110419 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80007, d110419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80007, d110419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80431 q = 1) (hb : d110420 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80431, d110420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80431, d110420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16800 (p : Pattern) (ha : d80441 p = 1) (hb : d110430 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d109496 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d80074 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d80437 q = 1) (hb : d110426 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80437, d110426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80437, d110426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d80438 q = 1) (hb : d110427 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80438, d110427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80438, d110427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d80439 q = 1) (hb : d110428 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80439, d110428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80439, d110428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80440 q = 1) (hb : d110429 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80440, d110429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80440, d110429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80441 q = 1) (hb : d110430 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80441, d110430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80441, d110430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16801 (p : Pattern) (ha : d80447 p = 1) (hb : d110436 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70488 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80009 q = 1) (hb : d110414 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80009, d110414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16797 q ha hb
    | true =>
      simp only [d80009, d110414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16798 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d109482 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d80010 q = 1) (hb : d110415 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80010, d110415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80010, d110415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d80429 q = 1) (hb : d110416 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80429, d110416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80429, d110416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80430 q = 1) (hb : d110417 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80430, d110417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80430, d110417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80432 q = 1) (hb : d110421 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80432, d110421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80432, d110421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16799 q ha hb
  have h8 (q : Pattern) (ha : d80433 q = 1) (hb : d110422 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80433, d110422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d80433, d110422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d80434 q = 1) (hb : d110423 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80434, d110423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d80434, d110423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d80435 q = 1) (hb : d110424 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80435, d110424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d80435, d110424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d80436 q = 1) (hb : d110425 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d80436, d110425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d80436, d110425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d80442 q = 1) (hb : d110431 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80442, d110431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80442, d110431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16800 q ha hb
  have h13 (q : Pattern) (ha : d80443 q = 1) (hb : d110432 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80443, d110432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d80443, d110432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d80444 q = 1) (hb : d110433 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80444, d110433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d80444, d110433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d80445 q = 1) (hb : d110434 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80445, d110434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d80445, d110434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d80446 q = 1) (hb : d110435 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d80446, d110435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d80446, d110435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d80447 q = 1) (hb : d110436 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d80447, d110436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d80447, d110436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro16802 (p : Pattern) (ha : d80453 p = 1) (hb : d110442 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80448 q = 1) (hb : d110437 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d80448, d110437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80448, d110437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16801 q ha hb
  have h2 (q : Pattern) (ha : d80449 q = 1) (hb : d110438 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d80449, d110438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80449, d110438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d80450 q = 1) (hb : d110439 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d80450, d110439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80450, d110439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d80451 q = 1) (hb : d110440 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d80451, d110440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80451, d110440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d80452 q = 1) (hb : d110441 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d80452, d110441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80452, d110441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80453 q = 1) (hb : d110442 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d80453, d110442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80453, d110442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16803 (p : Pattern) (ha : d80104 p = 1) (hb : d110450 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70591 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d70596 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d109519 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d80099 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d80100 q = 1) (hb : d110446 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80100, d110446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80100, d110446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d80101 q = 1) (hb : d110447 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80101, d110447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d80101, d110447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d80102 q = 1) (hb : d110448 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80102, d110448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80102, d110448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d80103 q = 1) (hb : d110449 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80103, d110449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80103, d110449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d80104 q = 1) (hb : d110450 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80104, d110450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80104, d110450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro16804 (p : Pattern) (ha : d80113 p = 1) (hb : d110455 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70591 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70596 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d109519 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d80099 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d80100 q = 1) (hb : d110446 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80100, d110446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80100, d110446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d80101 q = 1) (hb : d110447 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80101, d110447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80101, d110447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80102 q = 1) (hb : d110448 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80102, d110448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80102, d110448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d80103 q = 1) (hb : d110449 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80103, d110449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80103, d110449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d70612 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d70615 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d109525 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d80108 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d80109 q = 1) (hb : d110451 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80109, d110451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d80109, d110451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d80110 q = 1) (hb : d110452 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80110, d110452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d80110, d110452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h15 (q : Pattern) (ha : d80111 q = 1) (hb : d110453 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80111, d110453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d80111, d110453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d80112 q = 1) (hb : d110454 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80112, d110454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d80112, d110454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d80113 q = 1) (hb : d110455 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80113, d110455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d80113, d110455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro16805 (p : Pattern) (ha : d80459 p = 1) (hb : d110462 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d109525 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d80108 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d80109 q = 1) (hb : d110451 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80109, d110451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80109, d110451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d80110 q = 1) (hb : d110452 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80110, d110452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80110, d110452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d80111 q = 1) (hb : d110460 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80111, d110460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80111, d110460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80112 q = 1) (hb : d110461 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80112, d110461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80112, d110461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80459 q = 1) (hb : d110462 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80459, d110462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80459, d110462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16806 (p : Pattern) (ha : d80469 p = 1) (hb : d110472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d109547 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d80179 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d80465 q = 1) (hb : d110468 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80465, d110468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80465, d110468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d80466 q = 1) (hb : d110469 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80466, d110469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80466, d110469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d80467 q = 1) (hb : d110470 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80467, d110470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80467, d110470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80468 q = 1) (hb : d110471 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80468, d110471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80468, d110471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80469 q = 1) (hb : d110472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80469, d110472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80469, d110472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16807 (p : Pattern) (ha : d80475 p = 1) (hb : d110478 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70586 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80114 q = 1) (hb : d110456 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80114, d110456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16803 q ha hb
    | true =>
      simp only [d80114, d110456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16804 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d109533 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d80115 q = 1) (hb : d110457 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80115, d110457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80115, d110457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d80457 q = 1) (hb : d110458 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80457, d110458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80457, d110458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80458 q = 1) (hb : d110459 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80458, d110459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80458, d110459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80460 q = 1) (hb : d110463 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80460, d110463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80460, d110463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16805 q ha hb
  have h8 (q : Pattern) (ha : d80461 q = 1) (hb : d110464 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80461, d110464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d80461, d110464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d80462 q = 1) (hb : d110465 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80462, d110465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d80462, d110465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d80463 q = 1) (hb : d110466 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80463, d110466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d80463, d110466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d80464 q = 1) (hb : d110467 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d80464, d110467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d80464, d110467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d80470 q = 1) (hb : d110473 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80470, d110473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80470, d110473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16806 q ha hb
  have h13 (q : Pattern) (ha : d80471 q = 1) (hb : d110474 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80471, d110474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d80471, d110474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d80472 q = 1) (hb : d110475 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80472, d110475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d80472, d110475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d80473 q = 1) (hb : d110476 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80473, d110476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d80473, d110476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d80474 q = 1) (hb : d110477 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d80474, d110477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d80474, d110477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d80475 q = 1) (hb : d110478 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d80475, d110478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d80475, d110478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro16808 (p : Pattern) (ha : d80481 p = 1) (hb : d110484 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80476 q = 1) (hb : d110479 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d80476, d110479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80476, d110479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16807 q ha hb
  have h2 (q : Pattern) (ha : d80477 q = 1) (hb : d110480 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d80477, d110480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80477, d110480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d80478 q = 1) (hb : d110481 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d80478, d110481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80478, d110481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d80479 q = 1) (hb : d110482 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d80479, d110482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80479, d110482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d80480 q = 1) (hb : d110483 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d80480, d110483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80480, d110483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80481 q = 1) (hb : d110484 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d80481, d110484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80481, d110484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16809 (p : Pattern) (ha : d80210 p = 1) (hb : d110493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70690 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d70695 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d109571 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d80205 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d80206 q = 1) (hb : d110489 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80206, d110489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80206, d110489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d80207 q = 1) (hb : d110490 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80207, d110490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d80207, d110490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d80208 q = 1) (hb : d110491 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80208, d110491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80208, d110491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d80209 q = 1) (hb : d110492 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80209, d110492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80209, d110492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d80210 q = 1) (hb : d110493 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80210, d110493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80210, d110493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro16810 (p : Pattern) (ha : d80219 p = 1) (hb : d110498 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70690 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70695 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d109571 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d80205 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d80206 q = 1) (hb : d110489 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80206, d110489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80206, d110489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d80207 q = 1) (hb : d110490 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80207, d110490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80207, d110490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80208 q = 1) (hb : d110491 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80208, d110491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80208, d110491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d80209 q = 1) (hb : d110492 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80209, d110492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80209, d110492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d70711 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d70714 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d109577 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d80214 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d80215 q = 1) (hb : d110494 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80215, d110494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d80215, d110494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d80216 q = 1) (hb : d110495 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80216, d110495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d80216, d110495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h15 (q : Pattern) (ha : d80217 q = 1) (hb : d110496 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80217, d110496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d80217, d110496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d80218 q = 1) (hb : d110497 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80218, d110497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d80218, d110497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d80219 q = 1) (hb : d110498 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80219, d110498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d80219, d110498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro16811 (p : Pattern) (ha : d80488 p = 1) (hb : d110505 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d109577 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d80214 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d80215 q = 1) (hb : d110494 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80215, d110494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80215, d110494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d80216 q = 1) (hb : d110495 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80216, d110495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80216, d110495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d80217 q = 1) (hb : d110503 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80217, d110503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80217, d110503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80218 q = 1) (hb : d110504 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80218, d110504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80218, d110504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80488 q = 1) (hb : d110505 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80488, d110505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80488, d110505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16812 (p : Pattern) (ha : d80498 p = 1) (hb : d110515 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d109599 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d80285 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d80494 q = 1) (hb : d110511 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80494, d110511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80494, d110511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d80495 q = 1) (hb : d110512 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80495, d110512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80495, d110512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d80496 q = 1) (hb : d110513 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80496, d110513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80496, d110513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80497 q = 1) (hb : d110514 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80497, d110514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80497, d110514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80498 q = 1) (hb : d110515 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80498, d110515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80498, d110515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16813 (p : Pattern) (ha : d80504 p = 1) (hb : d110521 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70685 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80220 q = 1) (hb : d110499 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80220, d110499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16809 q ha hb
    | true =>
      simp only [d80220, d110499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16810 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d109585 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d80221 q = 1) (hb : d110500 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80221, d110500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80221, d110500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d80486 q = 1) (hb : d110501 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80486, d110501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80486, d110501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80487 q = 1) (hb : d110502 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80487, d110502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80487, d110502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80489 q = 1) (hb : d110506 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80489, d110506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80489, d110506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16811 q ha hb
  have h8 (q : Pattern) (ha : d80490 q = 1) (hb : d110507 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80490, d110507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d80490, d110507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d80491 q = 1) (hb : d110508 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80491, d110508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d80491, d110508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d80492 q = 1) (hb : d110509 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80492, d110509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d80492, d110509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d80493 q = 1) (hb : d110510 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d80493, d110510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d80493, d110510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d80499 q = 1) (hb : d110516 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80499, d110516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80499, d110516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16812 q ha hb
  have h13 (q : Pattern) (ha : d80500 q = 1) (hb : d110517 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80500, d110517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d80500, d110517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d80501 q = 1) (hb : d110518 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80501, d110518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d80501, d110518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d80502 q = 1) (hb : d110519 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80502, d110519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d80502, d110519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d80503 q = 1) (hb : d110520 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d80503, d110520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d80503, d110520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d80504 q = 1) (hb : d110521 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d80504, d110521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d80504, d110521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro16814 (p : Pattern) (ha : d80510 p = 1) (hb : d110527 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80505 q = 1) (hb : d110522 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d80505, d110522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80505, d110522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16813 q ha hb
  have h2 (q : Pattern) (ha : d80506 q = 1) (hb : d110523 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d80506, d110523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80506, d110523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d80507 q = 1) (hb : d110524 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d80507, d110524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80507, d110524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d80508 q = 1) (hb : d110525 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d80508, d110525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80508, d110525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d80509 q = 1) (hb : d110526 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d80509, d110526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80509, d110526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80510 q = 1) (hb : d110527 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d80510, d110527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80510, d110527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16815 (p : Pattern) (ha : d80516 p = 1) (hb : d110533 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d80401 q = 1) (hb : d110362 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d80401, d110362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16784 q ha hb
    | true =>
      simp only [d80401, d110362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16790 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d80427 q = 1) (hb : d110402 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d80427, d110402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80427, d110402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16796 q ha hb
  have h3 (q : Pattern) (ha : d80428 q = 1) (hb : d110403 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d80428, d110403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80428, d110403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d80454 q = 1) (hb : d110443 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d80454, d110443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80454, d110443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16802 q ha hb
  have h5 (q : Pattern) (ha : d80455 q = 1) (hb : d110444 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d80455, d110444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80455, d110444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80456 q = 1) (hb : d110445 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d80456, d110445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80456, d110445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80482 q = 1) (hb : d110485 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d80482, d110485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80482, d110485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16808 q ha hb
  have h8 (q : Pattern) (ha : d80483 q = 1) (hb : d110486 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d80483, d110486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80483, d110486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d80484 q = 1) (hb : d110487 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d80484, d110487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80484, d110487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d80485 q = 1) (hb : d110488 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d80485, d110488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d80485, d110488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d80511 q = 1) (hb : d110528 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d80511, d110528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80511, d110528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16814 q ha hb
  have h12 (q : Pattern) (ha : d80512 q = 1) (hb : d110529 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d80512, d110529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80512, d110529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d80513 q = 1) (hb : d110530 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d80513, d110530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80513, d110530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d80514 q = 1) (hb : d110531 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d80514, d110531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80514, d110531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d80515 q = 1) (hb : d110532 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d80515, d110532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d80515, d110532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d80516 q = 1) (hb : d110533 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d80516, d110533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d80516, d110533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro16816 (p : Pattern) (ha : d80522 p = 1) (hb : d110539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80517 q = 1) (hb : d110534 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d80517, d110534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16815 q ha hb
    | true =>
      simp only [d80517, d110534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d80518 q = 1) (hb : d110535 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d80518, d110535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80518, d110535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d80519 q = 1) (hb : d110536 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d80519, d110536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80519, d110536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d80520 q = 1) (hb : d110537 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d80520, d110537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80520, d110537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d80521 q = 1) (hb : d110538 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d80521, d110538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80521, d110538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d80522 q = 1) (hb : d110539 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d80522, d110539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d80522, d110539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16817 (p : Pattern) (ha : d80528 p = 1) (hb : d110545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80523 q = 1) (hb : d110540 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d80523, d110540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16816 q ha hb
    | true =>
      simp only [d80523, d110540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d80524 q = 1) (hb : d110541 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d80524, d110541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80524, d110541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d80525 q = 1) (hb : d110542 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d80525, d110542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80525, d110542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d80526 q = 1) (hb : d110543 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d80526, d110543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80526, d110543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d80527 q = 1) (hb : d110544 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d80527, d110544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80527, d110544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d80528 q = 1) (hb : d110545 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d80528, d110545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d80528, d110545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16818 (p : Pattern) (ha : d80534 p = 1) (hb : d110551 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80529 q = 1) (hb : d110546 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d80529, d110546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16817 q ha hb
    | true =>
      simp only [d80529, d110546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d80530 q = 1) (hb : d110547 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d80530, d110547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80530, d110547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d80531 q = 1) (hb : d110548 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d80531, d110548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80531, d110548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d80532 q = 1) (hb : d110549 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d80532, d110549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80532, d110549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d80533 q = 1) (hb : d110550 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d80533, d110550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80533, d110550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d80534 q = 1) (hb : d110551 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d80534, d110551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d80534, d110551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16819 (p : Pattern) (ha : d80540 p = 1) (hb : d110557 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80535 q = 1) (hb : d110552 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d80535, d110552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16818 q ha hb
    | true =>
      simp only [d80535, d110552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d80536 q = 1) (hb : d110553 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d80536, d110553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80536, d110553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d80537 q = 1) (hb : d110554 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d80537, d110554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80537, d110554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d80538 q = 1) (hb : d110555 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d80538, d110555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80538, d110555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d80539 q = 1) (hb : d110556 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d80539, d110556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80539, d110556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d80540 q = 1) (hb : d110557 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d80540, d110557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d80540, d110557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16820 (p : Pattern) (ha : d80546 p = 1) (hb : d110563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80541 q = 1) (hb : d110558 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d80541, d110558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16819 q ha hb
    | true =>
      simp only [d80541, d110558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d80542 q = 1) (hb : d110559 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d80542, d110559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80542, d110559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d80543 q = 1) (hb : d110560 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d80543, d110560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80543, d110560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d80544 q = 1) (hb : d110561 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d80544, d110561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80544, d110561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d80545 q = 1) (hb : d110562 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d80545, d110562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80545, d110562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d80546 q = 1) (hb : d110563 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d80546, d110563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d80546, d110563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16821 (p : Pattern) (ha : d80552 p = 1) (hb : d110569 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80547 q = 1) (hb : d110564 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d80547, d110564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16820 q ha hb
    | true =>
      simp only [d80547, d110564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d80548 q = 1) (hb : d110565 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d80548, d110565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80548, d110565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d80549 q = 1) (hb : d110566 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d80549, d110566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80549, d110566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d80550 q = 1) (hb : d110567 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d80550, d110567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80550, d110567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d80551 q = 1) (hb : d110568 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d80551, d110568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80551, d110568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d80552 q = 1) (hb : d110569 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d80552, d110569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d80552, d110569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16822 (p : Pattern) (ha : d80558 p = 1) (hb : d110575 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80553 q = 1) (hb : d110570 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d80553, d110570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16821 q ha hb
    | true =>
      simp only [d80553, d110570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d80554 q = 1) (hb : d110571 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d80554, d110571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80554, d110571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d80555 q = 1) (hb : d110572 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d80555, d110572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80555, d110572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d80556 q = 1) (hb : d110573 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d80556, d110573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80556, d110573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d80557 q = 1) (hb : d110574 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d80557, d110574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80557, d110574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d80558 q = 1) (hb : d110575 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d80558, d110575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d80558, d110575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16823 (p : Pattern) (ha : d7241 p = 1) (hb : d107483 p = 1) : d110577 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d144 q = 1) : d144 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d30 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d145 q = 1) (hb : d85721 q = 1) : d10649 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d85721, d10649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d145, d85721, d10649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d146 q = 1) (hb : d85721 q = 1) : d10650 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d10650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d10650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147 q = 1) (hb : d85721 q = 1) : d10651 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d10651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d10651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33 q = 1) (hb : d85721 q = 1) : d33 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d148 q = 1) (hb : d85721 q = 1) : d10652 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d10652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148, d10652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d7240 q = 1) (hb : d107483 q = 1) : d110576 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7240, d107483, d110576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7240, d107483, d110576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d7241 q = 1) (hb : d107483 q = 1) : d110577 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7241, d110577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7241, d110577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro16824 (p : Pattern) (ha : d7247 p = 1) (hb : d107483 p = 1) : d110583 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d107483 q = 1) : d110578 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16823 q ha hb
    | true =>
      simp only [d7242, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d107483 q = 1) : d110579 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d107483 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7244 q = 1) (hb : d107483 q = 1) : d110580 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7244, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7245 q = 1) (hb : d107483 q = 1) : d110581 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7245, d110581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7245, d110581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7246 q = 1) (hb : d107483 q = 1) : d110582 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7246, d110582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7246, d110582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7247 q = 1) (hb : d107483 q = 1) : d110583 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7247, d110583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7247, d110583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16825 (p : Pattern) (ha : d85394 p = 1) (hb : d107483 p = 1) : d110589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d107483 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d107483 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d107483 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7248 q = 1) (hb : d107483 q = 1) : d110584 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16824 q ha hb
    | true =>
      simp only [d7248, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85390 q = 1) (hb : d107483 q = 1) : d110585 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85390, d110585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85390, d110585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d107483 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d85391 q = 1) (hb : d107483 q = 1) : d110586 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85391, d110586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85391, d110586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85392 q = 1) (hb : d107483 q = 1) : d110587 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85392, d110587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85392, d110587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85393 q = 1) (hb : d107483 q = 1) : d110588 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85393, d110588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85393, d110588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85394 q = 1) (hb : d107483 q = 1) : d110589 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85394, d110589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85394, d110589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro16826 (p : Pattern) (ha : d7254 p = 1) (hb : d107483 p = 1) : d110590 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d107483 q = 1) : d110578 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16823 q ha hb
    | true =>
      simp only [d7242, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d107483 q = 1) : d110579 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d107483 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7244 q = 1) (hb : d107483 q = 1) : d110580 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7244, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7245 q = 1) (hb : d107483 q = 1) : d110581 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7245, d110581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7245, d110581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7246 q = 1) (hb : d107483 q = 1) : d110582 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7246, d110582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7246, d110582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7254 q = 1) (hb : d107483 q = 1) : d110590 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7254, d110590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7254, d110590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro16827 (p : Pattern) (ha : d85399 p = 1) (hb : d107483 p = 1) : d110596 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d107483 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d107483 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d107483 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7248 q = 1) (hb : d107483 q = 1) : d110584 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16824 q ha hb
    | true =>
      simp only [d7248, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85390 q = 1) (hb : d107483 q = 1) : d110585 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85390, d110585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85390, d110585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d107483 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d85391 q = 1) (hb : d107483 q = 1) : d110586 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85391, d110586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85391, d110586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85392 q = 1) (hb : d107483 q = 1) : d110587 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85392, d110587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85392, d110587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85393 q = 1) (hb : d107483 q = 1) : d110588 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85393, d110588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85393, d110588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d107483 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d107483 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d107483 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7255 q = 1) (hb : d107483 q = 1) : d110591 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7255, d110591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16826 q ha hb
    | true =>
      simp only [d7255, d110591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85395 q = 1) (hb : d107483 q = 1) : d110592 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85395, d110592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85395, d110592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d107483 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d85396 q = 1) (hb : d107483 q = 1) : d110593 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85396, d110593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85396, d110593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85397 q = 1) (hb : d107483 q = 1) : d110594 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85397, d110594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85397, d110594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d85398 q = 1) (hb : d107483 q = 1) : d110595 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85398, d110595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85398, d110595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d85399 q = 1) (hb : d107483 q = 1) : d110596 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85399, d110596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85399, d110596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro16828 (p : Pattern) (ha : d85406 p = 1) (hb : d107483 p = 1) : d110603 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d107483 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7255 q = 1) (hb : d107483 q = 1) : d110591 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7255, d110591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16826 q ha hb
    | true =>
      simp only [d7255, d110591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85395 q = 1) (hb : d107483 q = 1) : d110592 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85395, d110592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85395, d110592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d107483 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85396 q = 1) (hb : d107483 q = 1) : d110593 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85396, d110593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85396, d110593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85404 q = 1) (hb : d107483 q = 1) : d110601 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85404, d110601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85404, d110601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85405 q = 1) (hb : d107483 q = 1) : d110602 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85405, d110602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85405, d110602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85406 q = 1) (hb : d107483 q = 1) : d110603 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85406, d110603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85406, d110603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16829 (p : Pattern) (ha : d7274 p = 1) (hb : d107483 p = 1) : d110610 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d231 q = 1) : d231 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d232 q = 1) (hb : d85721 q = 1) : d10686 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d85721, d10686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d232, d85721, d10686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d233 q = 1) (hb : d85721 q = 1) : d10687 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d10687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d10687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234 q = 1) (hb : d85721 q = 1) : d10688 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d10688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d10688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74 q = 1) (hb : d85721 q = 1) : d74 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d235 q = 1) (hb : d85721 q = 1) : d10689 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d10689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d235, d10689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d7273 q = 1) (hb : d107483 q = 1) : d110609 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7273, d107483, d110609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7273, d107483, d110609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d7274 q = 1) (hb : d107483 q = 1) : d110610 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7274, d110610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7274, d110610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro16830 (p : Pattern) (ha : d7280 p = 1) (hb : d107483 p = 1) : d110616 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7275 q = 1) (hb : d107483 q = 1) : d110611 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7275, d110611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16829 q ha hb
    | true =>
      simp only [d7275, d110611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7276 q = 1) (hb : d107483 q = 1) : d110612 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7276, d110612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7276, d110612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d107483 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7277 q = 1) (hb : d107483 q = 1) : d110613 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7277, d110613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7277, d110613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7278 q = 1) (hb : d107483 q = 1) : d110614 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7278, d110614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7278, d110614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7279 q = 1) (hb : d107483 q = 1) : d110615 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7279, d110615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7279, d110615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7280 q = 1) (hb : d107483 q = 1) : d110616 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7280, d110616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7280, d110616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro16831 (p : Pattern) (ha : d85416 p = 1) (hb : d107483 p = 1) : d110622 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d107483 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7281 q = 1) (hb : d107483 q = 1) : d110617 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7281, d110617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16830 q ha hb
    | true =>
      simp only [d7281, d110617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85412 q = 1) (hb : d107483 q = 1) : d110618 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85412, d110618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85412, d110618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d107483 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85413 q = 1) (hb : d107483 q = 1) : d110619 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85413, d110619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85413, d110619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85414 q = 1) (hb : d107483 q = 1) : d110620 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85414, d110620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85414, d110620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85415 q = 1) (hb : d107483 q = 1) : d110621 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85415, d110621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85415, d110621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85416 q = 1) (hb : d107483 q = 1) : d110622 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85416, d110622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85416, d110622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16832 (p : Pattern) (ha : d85422 p = 1) (hb : d107483 p = 1) : d110628 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d107483 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85400 q = 1) (hb : d107483 q = 1) : d110597 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85400, d110597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16825 q ha hb
    | true =>
      simp only [d85400, d110597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16827 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d107483 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85401 q = 1) (hb : d107483 q = 1) : d110598 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85401, d110598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85401, d110598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85402 q = 1) (hb : d107483 q = 1) : d110599 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85402, d110599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85402, d110599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85403 q = 1) (hb : d107483 q = 1) : d110600 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85403, d110600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85403, d110600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85407 q = 1) (hb : d107483 q = 1) : d110604 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85407, d110604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85407, d110604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16828 q ha hb
  have h8 (q : Pattern) (ha : d85408 q = 1) (hb : d107483 q = 1) : d110605 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85408, d110605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85408, d110605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d85409 q = 1) (hb : d107483 q = 1) : d110606 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85409, d110606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85409, d110606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d85410 q = 1) (hb : d107483 q = 1) : d110607 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85410, d110607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85410, d110607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d85411 q = 1) (hb : d107483 q = 1) : d110608 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85411, d110608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85411, d110608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d85417 q = 1) (hb : d107483 q = 1) : d110623 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85417, d110623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85417, d110623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16831 q ha hb
  have h13 (q : Pattern) (ha : d85418 q = 1) (hb : d107483 q = 1) : d110624 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85418, d110624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85418, d110624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d85419 q = 1) (hb : d107483 q = 1) : d110625 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85419, d110625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85419, d110625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d85420 q = 1) (hb : d107483 q = 1) : d110626 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85420, d110626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85420, d110626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d85421 q = 1) (hb : d107483 q = 1) : d110627 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85421, d110627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85421, d110627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d85422 q = 1) (hb : d107483 q = 1) : d110628 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85422, d110628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85422, d110628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro16833 (p : Pattern) (ha : d7302 p = 1) (hb : d107483 p = 1) : d110638 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d107483 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7248 q = 1) (hb : d107483 q = 1) : d110584 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16824 q ha hb
    | true =>
      simp only [d7248, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7298 q = 1) (hb : d107483 q = 1) : d110634 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7298, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7298, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7299 q = 1) (hb : d107483 q = 1) : d110635 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7299, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7299, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7300 q = 1) (hb : d107483 q = 1) : d110636 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7300, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7300, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7301 q = 1) (hb : d107483 q = 1) : d110637 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7301, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7301, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7302 q = 1) (hb : d107483 q = 1) : d110638 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7302, d110638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7302, d110638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16834 (p : Pattern) (ha : d7309 p = 1) (hb : d107483 p = 1) : d110645 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d107483 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7248 q = 1) (hb : d107483 q = 1) : d110584 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16824 q ha hb
    | true =>
      simp only [d7248, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7298 q = 1) (hb : d107483 q = 1) : d110634 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7298, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7298, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7299 q = 1) (hb : d107483 q = 1) : d110635 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7299, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7299, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7300 q = 1) (hb : d107483 q = 1) : d110636 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7300, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7300, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7301 q = 1) (hb : d107483 q = 1) : d110637 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7301, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7301, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d107483 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7255 q = 1) (hb : d107483 q = 1) : d110591 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7255, d110591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16826 q ha hb
    | true =>
      simp only [d7255, d110591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7305 q = 1) (hb : d107483 q = 1) : d110641 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7305, d110641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7305, d110641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7306 q = 1) (hb : d107483 q = 1) : d110642 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7306, d110642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7306, d110642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d7307 q = 1) (hb : d107483 q = 1) : d110643 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7307, d110643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7307, d110643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d7308 q = 1) (hb : d107483 q = 1) : d110644 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7308, d110644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7308, d110644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d7309 q = 1) (hb : d107483 q = 1) : d110645 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7309, d110645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7309, d110645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro16835 (p : Pattern) (ha : d7376 p = 1) (hb : d107483 p = 1) : d110701 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d107483 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7248 q = 1) (hb : d107483 q = 1) : d110584 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16824 q ha hb
    | true =>
      simp only [d7248, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7298 q = 1) (hb : d107483 q = 1) : d110634 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7298, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7298, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7299 q = 1) (hb : d107483 q = 1) : d110635 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7299, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7299, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7300 q = 1) (hb : d107483 q = 1) : d110636 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7300, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7300, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7301 q = 1) (hb : d107483 q = 1) : d110637 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7301, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7301, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d107483 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7376 q = 1) (hb : d107483 q = 1) : d110701 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7376, d110701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7376, d110701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16836 (p : Pattern) (ha : d7314 p = 1) (hb : d107483 p = 1) : d110650 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d107483 q = 1) : d110578 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16823 q ha hb
    | true =>
      simp only [d7242, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d107483 q = 1) : d110579 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d107483 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7244 q = 1) (hb : d107483 q = 1) : d110580 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7244, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7245 q = 1) (hb : d107483 q = 1) : d110581 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7245, d110581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7245, d110581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7313 q = 1) (hb : d107483 q = 1) : d110649 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7313, d110649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7313, d110649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7314 q = 1) (hb : d107483 q = 1) : d110650 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7314, d110650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7314, d110650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16837 (p : Pattern) (ha : d7321 p = 1) (hb : d107483 p = 1) : d110657 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d107483 q = 1) : d110578 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16823 q ha hb
    | true =>
      simp only [d7242, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d107483 q = 1) : d110579 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d107483 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7244 q = 1) (hb : d107483 q = 1) : d110580 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7244, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7319 q = 1) (hb : d107483 q = 1) : d110655 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7319, d110655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7319, d110655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7320 q = 1) (hb : d107483 q = 1) : d110656 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7320, d110656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7320, d110656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7321 q = 1) (hb : d107483 q = 1) : d110657 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7321, d110657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7321, d110657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16838 (p : Pattern) (ha : d7326 p = 1) (hb : d107483 p = 1) : d110662 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d324 q = 1) : d324 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d144 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d325 q = 1) (hb : d85721 q = 1) : d10742 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d325, d85721, d10742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d325, d85721, d10742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d326 q = 1) (hb : d85721 q = 1) : d10743 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326, d10743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d326, d10743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d327 q = 1) (hb : d85721 q = 1) : d10744 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d327, d10744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d327, d10744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d144 q = 1) : d144 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d30 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d145 q = 1) (hb : d85721 q = 1) : d10649 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d85721, d10649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d145, d85721, d10649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d146 q = 1) (hb : d85721 q = 1) : d10650 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d10650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d10650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147 q = 1) (hb : d85721 q = 1) : d10651 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d10651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d10651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d328 q = 1) (hb : d85721 q = 1) : d10745 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d328, d10745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d328, d10745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7325 q = 1) (hb : d107483 q = 1) : d110661 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7325, d107483, d110661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7325, d107483, d110661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d7326 q = 1) (hb : d107483 q = 1) : d110662 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7326, d110662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d7326, d110662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro16839 (p : Pattern) (ha : d7332 p = 1) (hb : d107483 p = 1) : d110668 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d107483 q = 1) : d110663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16838 q ha hb
    | true =>
      simp only [d7327, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d107483 q = 1) : d110664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7242 q = 1) (hb : d107483 q = 1) : d110578 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16823 q ha hb
    | true =>
      simp only [d7242, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7243 q = 1) (hb : d107483 q = 1) : d110579 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7329 q = 1) (hb : d107483 q = 1) : d110665 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7329, d110665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7329, d110665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7330 q = 1) (hb : d107483 q = 1) : d110666 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7330, d110666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7330, d110666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7331 q = 1) (hb : d107483 q = 1) : d110667 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7331, d110667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7331, d110667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7332 q = 1) (hb : d107483 q = 1) : d110668 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7332, d110668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7332, d110668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16840 (p : Pattern) (ha : d7347 p = 1) (hb : d107483 p = 1) : d110674 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d107483 q = 1) : d110578 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16823 q ha hb
    | true =>
      simp only [d7242, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d107483 q = 1) : d110579 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7344 q = 1) (hb : d107483 q = 1) : d110671 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7344, d110671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7344, d110671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7345 q = 1) (hb : d107483 q = 1) : d110672 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7345, d110672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7345, d110672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7346 q = 1) (hb : d107483 q = 1) : d110673 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7346, d110673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7346, d110673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7347 q = 1) (hb : d107483 q = 1) : d110674 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7347, d110674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7347, d110674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16841 (p : Pattern) (ha : d85432 p = 1) (hb : d107483 p = 1) : d110680 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d107483 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7315 q = 1) (hb : d107483 q = 1) : d110651 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7315, d110651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16836 q ha hb
    | true =>
      simp only [d7315, d110651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7316 q = 1) (hb : d107483 q = 1) : d110652 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7316, d110652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7316, d110652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7317 q = 1) (hb : d107483 q = 1) : d110653 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7317, d110653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7317, d110653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7318 q = 1) (hb : d107483 q = 1) : d110654 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7318, d110654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7318, d110654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d107483 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7322 q = 1) (hb : d107483 q = 1) : d110658 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7322, d110658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16837 q ha hb
    | true =>
      simp only [d7322, d110658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7323 q = 1) (hb : d107483 q = 1) : d110659 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7323, d110659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7323, d110659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7324 q = 1) (hb : d107483 q = 1) : d110660 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7324, d110660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7324, d110660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7333 q = 1) (hb : d107483 q = 1) : d110669 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7333, d110669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16839 q ha hb
    | true =>
      simp only [d7333, d110669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16824 q ha hb
  have h11 (q : Pattern) (ha : d85428 q = 1) (hb : d107483 q = 1) : d110670 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85428, d110670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85428, d110670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7348 q = 1) (hb : d107483 q = 1) : d110675 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7348, d110675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16840 q ha hb
    | true =>
      simp only [d7348, d110675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d7349 q = 1) (hb : d107483 q = 1) : d110676 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7349, d110676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d7349, d110676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d85429 q = 1) (hb : d107483 q = 1) : d110677 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85429, d110677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85429, d110677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85430 q = 1) (hb : d107483 q = 1) : d110678 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85430, d110678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85430, d110678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d85431 q = 1) (hb : d107483 q = 1) : d110679 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85431, d110679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85431, d110679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85432 q = 1) (hb : d107483 q = 1) : d110680 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85432, d110680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85432, d110680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro16842 (p : Pattern) (ha : d7354 p = 1) (hb : d107483 p = 1) : d110681 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d107483 q = 1) : d110578 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16823 q ha hb
    | true =>
      simp only [d7242, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d107483 q = 1) : d110579 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d107483 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7244 q = 1) (hb : d107483 q = 1) : d110580 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7244, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7245 q = 1) (hb : d107483 q = 1) : d110581 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7245, d110581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7245, d110581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7313 q = 1) (hb : d107483 q = 1) : d110649 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7313, d110649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7313, d110649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7354 q = 1) (hb : d107483 q = 1) : d110681 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7354, d110681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7354, d110681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro16843 (p : Pattern) (ha : d7359 p = 1) (hb : d107483 p = 1) : d110686 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d107483 q = 1) : d110578 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16823 q ha hb
    | true =>
      simp only [d7242, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d107483 q = 1) : d110579 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d107483 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7244 q = 1) (hb : d107483 q = 1) : d110580 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7244, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7319 q = 1) (hb : d107483 q = 1) : d110655 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7319, d110655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7319, d110655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7320 q = 1) (hb : d107483 q = 1) : d110656 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7320, d110656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7320, d110656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7359 q = 1) (hb : d107483 q = 1) : d110686 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7359, d110686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7359, d110686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro16844 (p : Pattern) (ha : d7363 p = 1) (hb : d107483 p = 1) : d110690 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d107483 q = 1) : d110663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16838 q ha hb
    | true =>
      simp only [d7327, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d107483 q = 1) : d110664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7242 q = 1) (hb : d107483 q = 1) : d110578 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16823 q ha hb
    | true =>
      simp only [d7242, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7243 q = 1) (hb : d107483 q = 1) : d110579 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7329 q = 1) (hb : d107483 q = 1) : d110665 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7329, d110665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7329, d110665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7330 q = 1) (hb : d107483 q = 1) : d110666 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7330, d110666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7330, d110666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7331 q = 1) (hb : d107483 q = 1) : d110667 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7331, d110667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7331, d110667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7363 q = 1) (hb : d107483 q = 1) : d110690 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7363, d110690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7363, d110690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro16845 (p : Pattern) (ha : d7368 p = 1) (hb : d107483 p = 1) : d110693 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d107483 q = 1) : d110578 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16823 q ha hb
    | true =>
      simp only [d7242, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d107483 q = 1) : d110579 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7344 q = 1) (hb : d107483 q = 1) : d110671 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7344, d110671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7344, d110671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7345 q = 1) (hb : d107483 q = 1) : d110672 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7345, d110672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7345, d110672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7346 q = 1) (hb : d107483 q = 1) : d110673 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7346, d110673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7346, d110673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7368 q = 1) (hb : d107483 q = 1) : d110693 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7368, d110693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7368, d110693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16846 (p : Pattern) (ha : d85437 p = 1) (hb : d107483 p = 1) : d110699 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d107483 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7315 q = 1) (hb : d107483 q = 1) : d110651 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7315, d110651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16836 q ha hb
    | true =>
      simp only [d7315, d110651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7316 q = 1) (hb : d107483 q = 1) : d110652 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7316, d110652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7316, d110652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7317 q = 1) (hb : d107483 q = 1) : d110653 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7317, d110653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7317, d110653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7318 q = 1) (hb : d107483 q = 1) : d110654 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7318, d110654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7318, d110654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d107483 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7322 q = 1) (hb : d107483 q = 1) : d110658 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7322, d110658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16837 q ha hb
    | true =>
      simp only [d7322, d110658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7323 q = 1) (hb : d107483 q = 1) : d110659 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7323, d110659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7323, d110659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7324 q = 1) (hb : d107483 q = 1) : d110660 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7324, d110660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7324, d110660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7333 q = 1) (hb : d107483 q = 1) : d110669 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7333, d110669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16839 q ha hb
    | true =>
      simp only [d7333, d110669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16824 q ha hb
  have h11 (q : Pattern) (ha : d85428 q = 1) (hb : d107483 q = 1) : d110670 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85428, d110670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85428, d110670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7348 q = 1) (hb : d107483 q = 1) : d110675 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7348, d110675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16840 q ha hb
    | true =>
      simp only [d7348, d110675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d7349 q = 1) (hb : d107483 q = 1) : d110676 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7349, d110676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d7349, d110676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d85429 q = 1) (hb : d107483 q = 1) : d110677 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85429, d110677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85429, d110677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85430 q = 1) (hb : d107483 q = 1) : d110678 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85430, d110678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85430, d110678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d85431 q = 1) (hb : d107483 q = 1) : d110679 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85431, d110679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85431, d110679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d107483 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d7355 q = 1) (hb : d107483 q = 1) : d110682 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7355, d110682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16842 q ha hb
    | true =>
      simp only [d7355, d110682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d7356 q = 1) (hb : d107483 q = 1) : d110683 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7356, d110683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7356, d110683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d7357 q = 1) (hb : d107483 q = 1) : d110684 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7357, d110684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d7357, d110684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d7358 q = 1) (hb : d107483 q = 1) : d110685 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7358, d110685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7358, d110685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d107483 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d7360 q = 1) (hb : d107483 q = 1) : d110687 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7360, d110687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16843 q ha hb
    | true =>
      simp only [d7360, d110687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d7361 q = 1) (hb : d107483 q = 1) : d110688 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7361, d110688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7361, d110688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d7362 q = 1) (hb : d107483 q = 1) : d110689 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7362, d110689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d7362, d110689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d7364 q = 1) (hb : d107483 q = 1) : d110691 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7364, d110691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16844 q ha hb
    | true =>
      simp only [d7364, d110691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16826 q ha hb
  have h27 (q : Pattern) (ha : d85433 q = 1) (hb : d107483 q = 1) : d110692 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85433, d110692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d85433, d110692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d7369 q = 1) (hb : d107483 q = 1) : d110694 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7369, d110694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16845 q ha hb
    | true =>
      simp only [d7369, d110694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d7370 q = 1) (hb : d107483 q = 1) : d110695 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7370, d110695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d7370, d110695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d85434 q = 1) (hb : d107483 q = 1) : d110696 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85434, d110696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d85434, d110696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d85435 q = 1) (hb : d107483 q = 1) : d110697 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85435, d110697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d85435, d110697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d85436 q = 1) (hb : d107483 q = 1) : d110698 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85436, d110698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85436, d110698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d85437 q = 1) (hb : d107483 q = 1) : d110699 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85437, d110699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85437, d110699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro16847 (p : Pattern) (ha : d85444 p = 1) (hb : d107483 p = 1) : d110708 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7364 q = 1) (hb : d107483 q = 1) : d110691 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7364, d110691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16844 q ha hb
    | true =>
      simp only [d7364, d110691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16826 q ha hb
  have h2 (q : Pattern) (ha : d85433 q = 1) (hb : d107483 q = 1) : d110692 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85433, d110692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85433, d110692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7369 q = 1) (hb : d107483 q = 1) : d110694 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7369, d110694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16845 q ha hb
    | true =>
      simp only [d7369, d110694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7370 q = 1) (hb : d107483 q = 1) : d110695 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7370, d110695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7370, d110695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85434 q = 1) (hb : d107483 q = 1) : d110696 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85434, d110696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85434, d110696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85442 q = 1) (hb : d107483 q = 1) : d110706 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85442, d110706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85442, d110706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85443 q = 1) (hb : d107483 q = 1) : d110707 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85443, d110707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85443, d110707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85444 q = 1) (hb : d107483 q = 1) : d110708 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85444, d110708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85444, d110708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16848 (p : Pattern) (ha : d7390 p = 1) (hb : d107483 p = 1) : d110715 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d417 q = 1) : d417 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d231 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d418 q = 1) (hb : d85721 q = 1) : d10814 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, d85721, d10814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d418, d85721, d10814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d419 q = 1) (hb : d85721 q = 1) : d10815 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, d10815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d419, d10815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d420 q = 1) (hb : d85721 q = 1) : d10816 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, d10816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d420, d10816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d231 q = 1) : d231 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d71 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d232 q = 1) (hb : d85721 q = 1) : d10686 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d85721, d10686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d232, d85721, d10686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d233 q = 1) (hb : d85721 q = 1) : d10687 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d10687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d10687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d234 q = 1) (hb : d85721 q = 1) : d10688 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d10688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d10688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d421 q = 1) (hb : d85721 q = 1) : d10817 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d421, d10817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d421, d10817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7389 q = 1) (hb : d107483 q = 1) : d110714 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7389, d107483, d110714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7389, d107483, d110714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d7390 q = 1) (hb : d107483 q = 1) : d110715 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7390, d110715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d7390, d110715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro16849 (p : Pattern) (ha : d7396 p = 1) (hb : d107483 p = 1) : d110721 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7391 q = 1) (hb : d107483 q = 1) : d110716 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7391, d110716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16848 q ha hb
    | true =>
      simp only [d7391, d110716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7392 q = 1) (hb : d107483 q = 1) : d110717 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7392, d110717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7392, d110717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7275 q = 1) (hb : d107483 q = 1) : d110611 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7275, d110611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16829 q ha hb
    | true =>
      simp only [d7275, d110611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7276 q = 1) (hb : d107483 q = 1) : d110612 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7276, d110612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7276, d110612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7393 q = 1) (hb : d107483 q = 1) : d110718 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7393, d110718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7393, d110718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7394 q = 1) (hb : d107483 q = 1) : d110719 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7394, d110719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7394, d110719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7395 q = 1) (hb : d107483 q = 1) : d110720 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7395, d110720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7395, d110720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7396 q = 1) (hb : d107483 q = 1) : d110721 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7396, d110721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7396, d110721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro16850 (p : Pattern) (ha : d7411 p = 1) (hb : d107483 p = 1) : d110727 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7275 q = 1) (hb : d107483 q = 1) : d110611 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7275, d110611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16829 q ha hb
    | true =>
      simp only [d7275, d110611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7276 q = 1) (hb : d107483 q = 1) : d110612 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7276, d110612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7276, d110612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7408 q = 1) (hb : d107483 q = 1) : d110724 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7408, d110724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7408, d110724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7409 q = 1) (hb : d107483 q = 1) : d110725 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7409, d110725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7409, d110725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7410 q = 1) (hb : d107483 q = 1) : d110726 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7410, d110726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7410, d110726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7411 q = 1) (hb : d107483 q = 1) : d110727 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7411, d110727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7411, d110727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16851 (p : Pattern) (ha : d85454 p = 1) (hb : d107483 p = 1) : d110733 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7397 q = 1) (hb : d107483 q = 1) : d110722 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7397, d110722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16849 q ha hb
    | true =>
      simp only [d7397, d110722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16830 q ha hb
  have h2 (q : Pattern) (ha : d85450 q = 1) (hb : d107483 q = 1) : d110723 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85450, d110723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85450, d110723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7412 q = 1) (hb : d107483 q = 1) : d110728 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7412, d110728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16850 q ha hb
    | true =>
      simp only [d7412, d110728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7413 q = 1) (hb : d107483 q = 1) : d110729 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7413, d110729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7413, d110729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85451 q = 1) (hb : d107483 q = 1) : d110730 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85451, d110730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85451, d110730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85452 q = 1) (hb : d107483 q = 1) : d110731 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85452, d110731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85452, d110731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85453 q = 1) (hb : d107483 q = 1) : d110732 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85453, d110732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85453, d110732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85454 q = 1) (hb : d107483 q = 1) : d110733 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85454, d110733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85454, d110733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16852 (p : Pattern) (ha : d85460 p = 1) (hb : d107483 p = 1) : d110739 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7303 q = 1) (hb : d107483 q = 1) : d110639 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7303, d110639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7303, d110639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16833 q ha hb
  have h2 (q : Pattern) (ha : d7304 q = 1) (hb : d107483 q = 1) : d110640 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7304, d110640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7304, d110640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7310 q = 1) (hb : d107483 q = 1) : d110646 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7310, d110646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16833 q ha hb
    | true =>
      simp only [d7310, d110646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16834 q ha hb
  have h4 (q : Pattern) (ha : d7311 q = 1) (hb : d107483 q = 1) : d110647 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7311, d110647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7311, d110647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7312 q = 1) (hb : d107483 q = 1) : d110648 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7312, d110648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7312, d110648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85438 q = 1) (hb : d107483 q = 1) : d110700 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85438, d110700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16841 q ha hb
    | true =>
      simp only [d85438, d110700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16846 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d107483 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7377 q = 1) (hb : d107483 q = 1) : d110702 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7377, d110702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16835 q ha hb
    | true =>
      simp only [d7377, d110702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85439 q = 1) (hb : d107483 q = 1) : d110703 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85439, d110703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85439, d110703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85440 q = 1) (hb : d107483 q = 1) : d110704 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85440, d110704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85440, d110704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d85441 q = 1) (hb : d107483 q = 1) : d110705 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85441, d110705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85441, d110705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d85445 q = 1) (hb : d107483 q = 1) : d110709 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85445, d110709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85445, d110709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16847 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d107483 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d85446 q = 1) (hb : d107483 q = 1) : d110710 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85446, d110710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85446, d110710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85447 q = 1) (hb : d107483 q = 1) : d110711 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85447, d110711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85447, d110711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d85448 q = 1) (hb : d107483 q = 1) : d110712 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85448, d110712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85448, d110712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d85449 q = 1) (hb : d107483 q = 1) : d110713 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85449, d110713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85449, d110713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d85455 q = 1) (hb : d107483 q = 1) : d110734 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85455, d110734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85455, d110734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16851 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d107483 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d85456 q = 1) (hb : d107483 q = 1) : d110735 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85456, d110735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d85456, d110735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d85457 q = 1) (hb : d107483 q = 1) : d110736 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85457, d110736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d85457, d110736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d85458 q = 1) (hb : d107483 q = 1) : d110737 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85458, d110737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85458, d110737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d85459 q = 1) (hb : d107483 q = 1) : d110738 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85459, d110738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d85459, d110738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d85460 q = 1) (hb : d107483 q = 1) : d110739 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85460, d110739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85460, d110739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro16853 (p : Pattern) (ha : d85466 p = 1) (hb : d107483 p = 1) : d110745 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d107483 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d85423 q = 1) (hb : d107483 q = 1) : d110629 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85423, d110629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85423, d110629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16832 q ha hb
  have h3 (q : Pattern) (ha : d85424 q = 1) (hb : d107483 q = 1) : d110630 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85424, d110630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85424, d110630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85425 q = 1) (hb : d107483 q = 1) : d110631 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85425, d110631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85425, d110631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85426 q = 1) (hb : d107483 q = 1) : d110632 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85426, d110632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85426, d110632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85427 q = 1) (hb : d107483 q = 1) : d110633 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85427, d110633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85427, d110633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85461 q = 1) (hb : d107483 q = 1) : d110740 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85461, d110740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85461, d110740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16852 q ha hb
  have h8 (q : Pattern) (ha : d85462 q = 1) (hb : d107483 q = 1) : d110741 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85462, d110741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85462, d110741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85463 q = 1) (hb : d107483 q = 1) : d110742 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85463, d110742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85463, d110742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85464 q = 1) (hb : d107483 q = 1) : d110743 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85464, d110743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85464, d110743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d85465 q = 1) (hb : d107483 q = 1) : d110744 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85465, d110744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85465, d110744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d85466 q = 1) (hb : d107483 q = 1) : d110745 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85466, d110745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85466, d110745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro16854 (p : Pattern) (ha : d481 p = 1) (hb : d107483 p = 1) : d10869 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d144 q = 1) : d144 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d30 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d145 q = 1) (hb : d85721 q = 1) : d10649 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d85721, d10649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d145, d85721, d10649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d146 q = 1) (hb : d85721 q = 1) : d10650 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d10650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d10650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147 q = 1) (hb : d85721 q = 1) : d10651 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d10651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d10651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d475 q = 1) (hb : d85721 q = 1) : d10863 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d10863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d475, d10863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d480 q = 1) (hb : d107483 q = 1) : d10868 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d480, d107483, d10868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d480, d107483, d10868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d481 q = 1) (hb : d107483 q = 1) : d10869 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d481, d10869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d481, d10869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro16855 (p : Pattern) (ha : d491 p = 1) (hb : d107483 p = 1) : d10879 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d107483 q = 1) : d10870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16854 q ha hb
    | true =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d107483 q = 1) : d10871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d107483 q = 1) : d10876 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d10876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d10876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d107483 q = 1) : d10877 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d10877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d10877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d107483 q = 1) : d10878 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d10878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d10878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d491 q = 1) (hb : d107483 q = 1) : d10879 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d491, d10879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d491, d10879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16856 (p : Pattern) (ha : d501 p = 1) (hb : d107483 p = 1) : d10889 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d107483 q = 1) : d10870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16854 q ha hb
    | true =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d107483 q = 1) : d10871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d107483 q = 1) : d10876 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d10876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d10876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d107483 q = 1) : d10877 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d10877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d10877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d107483 q = 1) : d10878 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d10878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d10878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d501 q = 1) (hb : d107483 q = 1) : d10889 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d501, d10889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d501, d10889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16857 (p : Pattern) (ha : d644 p = 1) (hb : d107483 p = 1) : d10998 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d633 q = 1) (hb : d107483 q = 1) : d10987 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d10987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16855 q ha hb
    | true =>
      simp only [d633, d10987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d634 q = 1) (hb : d107483 q = 1) : d10988 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d10988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d10988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d635 q = 1) (hb : d107483 q = 1) : d10989 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d10989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d635, d10989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d636 q = 1) (hb : d107483 q = 1) : d10990 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d10990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d10990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d637 q = 1) (hb : d107483 q = 1) : d10991 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d10991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d10991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d639 q = 1) (hb : d107483 q = 1) : d10993 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d10993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16856 q ha hb
    | true =>
      simp only [d639, d10993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d640 q = 1) (hb : d107483 q = 1) : d10994 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d10994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, d10994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d641 q = 1) (hb : d107483 q = 1) : d10995 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d10995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d641, d10995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d642 q = 1) (hb : d107483 q = 1) : d10996 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d10996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, d10996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d643 q = 1) (hb : d107483 q = 1) : d10997 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d10997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d10997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d644 q = 1) (hb : d107483 q = 1) : d10998 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d644, d10998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d644, d10998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro16858 (p : Pattern) (ha : d653 p = 1) (hb : d107483 p = 1) : d11007 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d639 q = 1) (hb : d107483 q = 1) : d10993 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d10993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16856 q ha hb
    | true =>
      simp only [d639, d10993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d640 q = 1) (hb : d107483 q = 1) : d10994 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d10994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, d10994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d641 q = 1) (hb : d107483 q = 1) : d10995 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d10995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d641, d10995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d642 q = 1) (hb : d107483 q = 1) : d10996 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d10996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, d10996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d643 q = 1) (hb : d107483 q = 1) : d10997 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d10997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d10997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d653 q = 1) (hb : d107483 q = 1) : d11007 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d653, d11007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d653, d11007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16859 (p : Pattern) (ha : d683 p = 1) (hb : d107483 p = 1) : d11031 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d231 q = 1) : d231 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d232 q = 1) (hb : d85721 q = 1) : d10686 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d85721, d10686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d232, d85721, d10686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d233 q = 1) (hb : d85721 q = 1) : d10687 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d10687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d10687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234 q = 1) (hb : d85721 q = 1) : d10688 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d10688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d10688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d673 q = 1) (hb : d85721 q = 1) : d11021 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d11021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d673, d11021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d682 q = 1) (hb : d107483 q = 1) : d11030 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d682, d107483, d11030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d682, d107483, d11030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d683 q = 1) (hb : d107483 q = 1) : d11031 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d683, d11031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d683, d11031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro16860 (p : Pattern) (ha : d730 p = 1) (hb : d107483 p = 1) : d11076 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d684 q = 1) (hb : d107483 q = 1) : d11032 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d11032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16859 q ha hb
    | true =>
      simp only [d684, d11032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d685 q = 1) (hb : d107483 q = 1) : d11033 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d11033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d11033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d727 q = 1) (hb : d107483 q = 1) : d11073 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d727, d11073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d727, d11073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d728 q = 1) (hb : d107483 q = 1) : d11074 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d728, d11074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d728, d11074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d729 q = 1) (hb : d107483 q = 1) : d11075 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d729, d11075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d729, d11075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d730 q = 1) (hb : d107483 q = 1) : d11076 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d730, d11076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d730, d11076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16861 (p : Pattern) (ha : d736 p = 1) (hb : d107483 p = 1) : d11082 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d731 q = 1) (hb : d107483 q = 1) : d11077 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d731, d11077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16860 q ha hb
    | true =>
      simp only [d731, d11077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d732 q = 1) (hb : d107483 q = 1) : d11078 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d732, d11078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d732, d11078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d733 q = 1) (hb : d107483 q = 1) : d11079 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d733, d11079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d733, d11079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d734 q = 1) (hb : d107483 q = 1) : d11080 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d734, d11080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d734, d11080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d735 q = 1) (hb : d107483 q = 1) : d11081 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d735, d11081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d735, d11081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d736 q = 1) (hb : d107483 q = 1) : d11082 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d736, d11082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d736, d11082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16862 (p : Pattern) (ha : d7433 p = 1) (hb : d107483 p = 1) : d110749 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d107483 q = 1) : d110663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16838 q ha hb
    | true =>
      simp only [d7327, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d107483 q = 1) : d110664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d107483 q = 1) : d10870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16854 q ha hb
    | true =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d107483 q = 1) : d10871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7430 q = 1) (hb : d107483 q = 1) : d110746 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7430, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7431 q = 1) (hb : d107483 q = 1) : d110747 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7431, d110747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7431, d110747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7432 q = 1) (hb : d107483 q = 1) : d110748 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7432, d110748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7432, d110748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7433 q = 1) (hb : d107483 q = 1) : d110749 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7433, d110749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7433, d110749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16863 (p : Pattern) (ha : d7439 p = 1) (hb : d107483 p = 1) : d110755 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7434 q = 1) (hb : d107483 q = 1) : d110750 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7434, d110750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16862 q ha hb
    | true =>
      simp only [d7434, d110750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16855 q ha hb
  have h2 (q : Pattern) (ha : d7435 q = 1) (hb : d107483 q = 1) : d110751 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7435, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7435, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7436 q = 1) (hb : d107483 q = 1) : d110752 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7436, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7436, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7437 q = 1) (hb : d107483 q = 1) : d110753 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7437, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7437, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7438 q = 1) (hb : d107483 q = 1) : d110754 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7438, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7438, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7439 q = 1) (hb : d107483 q = 1) : d110755 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7439, d110755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7439, d110755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16864 (p : Pattern) (ha : d7442 p = 1) (hb : d107483 p = 1) : d110758 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d107483 q = 1) : d110663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16838 q ha hb
    | true =>
      simp only [d7327, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d107483 q = 1) : d110664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d107483 q = 1) : d10870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16854 q ha hb
    | true =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d107483 q = 1) : d10871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7430 q = 1) (hb : d107483 q = 1) : d110746 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7430, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7431 q = 1) (hb : d107483 q = 1) : d110747 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7431, d110747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7431, d110747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7432 q = 1) (hb : d107483 q = 1) : d110748 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7432, d110748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7432, d110748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7442 q = 1) (hb : d107483 q = 1) : d110758 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7442, d110758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7442, d110758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro16865 (p : Pattern) (ha : d7448 p = 1) (hb : d107483 p = 1) : d110764 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7434 q = 1) (hb : d107483 q = 1) : d110750 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7434, d110750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16862 q ha hb
    | true =>
      simp only [d7434, d110750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16855 q ha hb
  have h2 (q : Pattern) (ha : d7435 q = 1) (hb : d107483 q = 1) : d110751 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7435, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7435, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7436 q = 1) (hb : d107483 q = 1) : d110752 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7436, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7436, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7437 q = 1) (hb : d107483 q = 1) : d110753 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7437, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7437, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7438 q = 1) (hb : d107483 q = 1) : d110754 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7438, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7438, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7443 q = 1) (hb : d107483 q = 1) : d110759 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7443, d110759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16864 q ha hb
    | true =>
      simp only [d7443, d110759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16856 q ha hb
  have h7 (q : Pattern) (ha : d7444 q = 1) (hb : d107483 q = 1) : d110760 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7444, d110760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7444, d110760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7445 q = 1) (hb : d107483 q = 1) : d110761 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7445, d110761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7445, d110761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d7446 q = 1) (hb : d107483 q = 1) : d110762 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7446, d110762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7446, d110762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7447 q = 1) (hb : d107483 q = 1) : d110763 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7447, d110763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7447, d110763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7448 q = 1) (hb : d107483 q = 1) : d110764 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7448, d110764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7448, d110764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro16866 (p : Pattern) (ha : d7515 p = 1) (hb : d107483 p = 1) : d110820 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7434 q = 1) (hb : d107483 q = 1) : d110750 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7434, d110750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16862 q ha hb
    | true =>
      simp only [d7434, d110750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16855 q ha hb
  have h2 (q : Pattern) (ha : d7435 q = 1) (hb : d107483 q = 1) : d110751 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7435, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7435, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7436 q = 1) (hb : d107483 q = 1) : d110752 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7436, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7436, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7437 q = 1) (hb : d107483 q = 1) : d110753 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7437, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7437, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7438 q = 1) (hb : d107483 q = 1) : d110754 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7438, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7438, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d633 q = 1) (hb : d107483 q = 1) : d10987 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d10987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16855 q ha hb
    | true =>
      simp only [d633, d10987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d634 q = 1) (hb : d107483 q = 1) : d10988 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d10988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d10988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d635 q = 1) (hb : d107483 q = 1) : d10989 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d10989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d635, d10989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d636 q = 1) (hb : d107483 q = 1) : d10990 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d10990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d10990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d637 q = 1) (hb : d107483 q = 1) : d10991 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d10991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d10991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7515 q = 1) (hb : d107483 q = 1) : d110820 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7515, d110820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7515, d110820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro16867 (p : Pattern) (ha : d514 p = 1) (hb : d107483 p = 1) : d10902 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d107483 q = 1) : d10870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16854 q ha hb
    | true =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d107483 q = 1) : d10871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d107483 q = 1) : d10876 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d10876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d10876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d107483 q = 1) : d10877 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d10877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d10877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d513 q = 1) (hb : d107483 q = 1) : d10901 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d10901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d10901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d514 q = 1) (hb : d107483 q = 1) : d10902 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d514, d10902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d514, d10902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16868 (p : Pattern) (ha : d524 p = 1) (hb : d107483 p = 1) : d10912 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d107483 q = 1) : d10870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16854 q ha hb
    | true =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d107483 q = 1) : d10871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d107483 q = 1) : d10876 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d10876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d10876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d522 q = 1) (hb : d107483 q = 1) : d10910 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d10910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d10910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d523 q = 1) (hb : d107483 q = 1) : d10911 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d10911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d523, d10911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d524 q = 1) (hb : d107483 q = 1) : d10912 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d524, d10912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d524, d10912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16869 (p : Pattern) (ha : d7453 p = 1) (hb : d107483 p = 1) : d110769 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d107483 q = 1) : d110663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16838 q ha hb
    | true =>
      simp only [d7327, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d107483 q = 1) : d110664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d107483 q = 1) : d10870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16854 q ha hb
    | true =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d107483 q = 1) : d10871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7430 q = 1) (hb : d107483 q = 1) : d110746 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7430, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7431 q = 1) (hb : d107483 q = 1) : d110747 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7431, d110747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7431, d110747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7452 q = 1) (hb : d107483 q = 1) : d110768 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7452, d110768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7452, d110768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7453 q = 1) (hb : d107483 q = 1) : d110769 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7453, d110769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7453, d110769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16870 (p : Pattern) (ha : d7460 p = 1) (hb : d107483 p = 1) : d110776 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d107483 q = 1) : d110663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16838 q ha hb
    | true =>
      simp only [d7327, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d107483 q = 1) : d110664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d107483 q = 1) : d10870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16854 q ha hb
    | true =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d107483 q = 1) : d10871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7430 q = 1) (hb : d107483 q = 1) : d110746 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7430, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7458 q = 1) (hb : d107483 q = 1) : d110774 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7458, d110774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7458, d110774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7459 q = 1) (hb : d107483 q = 1) : d110775 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7459, d110775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7459, d110775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7460 q = 1) (hb : d107483 q = 1) : d110776 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7460, d110776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7460, d110776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16871 (p : Pattern) (ha : d7465 p = 1) (hb : d107483 p = 1) : d110781 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d548 q = 1) : d548 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d324 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d549 q = 1) (hb : d85721 q = 1) : d10916 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d549, d85721, d10916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d549, d85721, d10916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d550 q = 1) (hb : d85721 q = 1) : d10917 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d550, d10917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d550, d10917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d551 q = 1) (hb : d85721 q = 1) : d10918 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d551, d10918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d551, d10918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d324 q = 1) : d324 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d144 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d325 q = 1) (hb : d85721 q = 1) : d10742 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d325, d85721, d10742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d325, d85721, d10742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d326 q = 1) (hb : d85721 q = 1) : d10743 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326, d10743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d326, d10743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d327 q = 1) (hb : d85721 q = 1) : d10744 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d327, d10744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d327, d10744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d552 q = 1) (hb : d85721 q = 1) : d10919 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d552, d10919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d552, d10919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7464 q = 1) (hb : d107483 q = 1) : d110780 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7464, d107483, d110780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7464, d107483, d110780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d7465 q = 1) (hb : d107483 q = 1) : d110781 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7465, d110781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d7465, d110781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro16872 (p : Pattern) (ha : d7471 p = 1) (hb : d107483 p = 1) : d110787 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7466 q = 1) (hb : d107483 q = 1) : d110782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7466, d110782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16871 q ha hb
    | true =>
      simp only [d7466, d110782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7467 q = 1) (hb : d107483 q = 1) : d110783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7467, d110783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7467, d110783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7327 q = 1) (hb : d107483 q = 1) : d110663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16838 q ha hb
    | true =>
      simp only [d7327, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7328 q = 1) (hb : d107483 q = 1) : d110664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7468 q = 1) (hb : d107483 q = 1) : d110784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7468, d110784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7468, d110784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7469 q = 1) (hb : d107483 q = 1) : d110785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7469, d110785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7469, d110785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7470 q = 1) (hb : d107483 q = 1) : d110786 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7470, d110786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7470, d110786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7471 q = 1) (hb : d107483 q = 1) : d110787 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7471, d110787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7471, d110787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16873 (p : Pattern) (ha : d7486 p = 1) (hb : d107483 p = 1) : d110793 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d107483 q = 1) : d110663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16838 q ha hb
    | true =>
      simp only [d7327, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d107483 q = 1) : d110664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7483 q = 1) (hb : d107483 q = 1) : d110790 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7483, d110790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7483, d110790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7484 q = 1) (hb : d107483 q = 1) : d110791 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7484, d110791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7484, d110791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7485 q = 1) (hb : d107483 q = 1) : d110792 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7485, d110792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7485, d110792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7486 q = 1) (hb : d107483 q = 1) : d110793 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7486, d110793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7486, d110793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16874 (p : Pattern) (ha : d85471 p = 1) (hb : d107483 p = 1) : d110799 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7454 q = 1) (hb : d107483 q = 1) : d110770 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7454, d110770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16869 q ha hb
    | true =>
      simp only [d7454, d110770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16867 q ha hb
  have h2 (q : Pattern) (ha : d7455 q = 1) (hb : d107483 q = 1) : d110771 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7455, d110771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7455, d110771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7456 q = 1) (hb : d107483 q = 1) : d110772 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7456, d110772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7456, d110772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7457 q = 1) (hb : d107483 q = 1) : d110773 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7457, d110773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7457, d110773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7461 q = 1) (hb : d107483 q = 1) : d110777 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7461, d110777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16870 q ha hb
    | true =>
      simp only [d7461, d110777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16868 q ha hb
  have h6 (q : Pattern) (ha : d7462 q = 1) (hb : d107483 q = 1) : d110778 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7462, d110778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7462, d110778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7463 q = 1) (hb : d107483 q = 1) : d110779 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7463, d110779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7463, d110779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7472 q = 1) (hb : d107483 q = 1) : d110788 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7472, d110788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16872 q ha hb
    | true =>
      simp only [d7472, d110788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16862 q ha hb
  have h9 (q : Pattern) (ha : d85467 q = 1) (hb : d107483 q = 1) : d110789 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85467, d110789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85467, d110789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7487 q = 1) (hb : d107483 q = 1) : d110794 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7487, d110794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16873 q ha hb
    | true =>
      simp only [d7487, d110794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d7488 q = 1) (hb : d107483 q = 1) : d110795 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7488, d110795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7488, d110795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d85468 q = 1) (hb : d107483 q = 1) : d110796 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85468, d110796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85468, d110796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85469 q = 1) (hb : d107483 q = 1) : d110797 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85469, d110797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85469, d110797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85470 q = 1) (hb : d107483 q = 1) : d110798 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85470, d110798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85470, d110798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85471 q = 1) (hb : d107483 q = 1) : d110799 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85471, d110799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85471, d110799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro16875 (p : Pattern) (ha : d610 p = 1) (hb : d107483 p = 1) : d10963 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d107483 q = 1) : d10870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16854 q ha hb
    | true =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d107483 q = 1) : d10871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d107483 q = 1) : d10876 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d10876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d10876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d107483 q = 1) : d10877 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d10877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d10877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d513 q = 1) (hb : d107483 q = 1) : d10901 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d10901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d10901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d610 q = 1) (hb : d107483 q = 1) : d10963 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d610, d10963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d610, d10963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16876 (p : Pattern) (ha : d616 p = 1) (hb : d107483 p = 1) : d10969 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d107483 q = 1) : d10870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16854 q ha hb
    | true =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d107483 q = 1) : d10871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d107483 q = 1) : d10876 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d10876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d10876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d522 q = 1) (hb : d107483 q = 1) : d10910 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d10910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d10910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d523 q = 1) (hb : d107483 q = 1) : d10911 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d10911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d523, d10911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d616 q = 1) (hb : d107483 q = 1) : d10969 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d616, d10969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d616, d10969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16877 (p : Pattern) (ha : d7493 p = 1) (hb : d107483 p = 1) : d110800 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d107483 q = 1) : d110663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16838 q ha hb
    | true =>
      simp only [d7327, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d107483 q = 1) : d110664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d107483 q = 1) : d10870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16854 q ha hb
    | true =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d107483 q = 1) : d10871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7430 q = 1) (hb : d107483 q = 1) : d110746 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7430, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7431 q = 1) (hb : d107483 q = 1) : d110747 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7431, d110747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7431, d110747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7452 q = 1) (hb : d107483 q = 1) : d110768 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7452, d110768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7452, d110768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7493 q = 1) (hb : d107483 q = 1) : d110800 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7493, d110800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7493, d110800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro16878 (p : Pattern) (ha : d7498 p = 1) (hb : d107483 p = 1) : d110805 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d107483 q = 1) : d110663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16838 q ha hb
    | true =>
      simp only [d7327, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d107483 q = 1) : d110664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d107483 q = 1) : d10870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16854 q ha hb
    | true =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d107483 q = 1) : d10871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7430 q = 1) (hb : d107483 q = 1) : d110746 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7430, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7458 q = 1) (hb : d107483 q = 1) : d110774 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7458, d110774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7458, d110774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7459 q = 1) (hb : d107483 q = 1) : d110775 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7459, d110775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7459, d110775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7498 q = 1) (hb : d107483 q = 1) : d110805 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7498, d110805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7498, d110805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro16879 (p : Pattern) (ha : d7502 p = 1) (hb : d107483 p = 1) : d110809 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7466 q = 1) (hb : d107483 q = 1) : d110782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7466, d110782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16871 q ha hb
    | true =>
      simp only [d7466, d110782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7467 q = 1) (hb : d107483 q = 1) : d110783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7467, d110783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7467, d110783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7327 q = 1) (hb : d107483 q = 1) : d110663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16838 q ha hb
    | true =>
      simp only [d7327, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7328 q = 1) (hb : d107483 q = 1) : d110664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7468 q = 1) (hb : d107483 q = 1) : d110784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7468, d110784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7468, d110784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7469 q = 1) (hb : d107483 q = 1) : d110785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7469, d110785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7469, d110785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7470 q = 1) (hb : d107483 q = 1) : d110786 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7470, d110786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7470, d110786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7502 q = 1) (hb : d107483 q = 1) : d110809 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7502, d110809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7502, d110809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro16880 (p : Pattern) (ha : d7507 p = 1) (hb : d107483 p = 1) : d110812 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d107483 q = 1) : d110663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16838 q ha hb
    | true =>
      simp only [d7327, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d107483 q = 1) : d110664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7483 q = 1) (hb : d107483 q = 1) : d110790 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7483, d110790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7483, d110790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7484 q = 1) (hb : d107483 q = 1) : d110791 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7484, d110791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7484, d110791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7485 q = 1) (hb : d107483 q = 1) : d110792 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7485, d110792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7485, d110792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7507 q = 1) (hb : d107483 q = 1) : d110812 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7507, d110812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7507, d110812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16881 (p : Pattern) (ha : d85476 p = 1) (hb : d107483 p = 1) : d110818 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7454 q = 1) (hb : d107483 q = 1) : d110770 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7454, d110770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16869 q ha hb
    | true =>
      simp only [d7454, d110770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16867 q ha hb
  have h2 (q : Pattern) (ha : d7455 q = 1) (hb : d107483 q = 1) : d110771 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7455, d110771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7455, d110771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7456 q = 1) (hb : d107483 q = 1) : d110772 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7456, d110772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7456, d110772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7457 q = 1) (hb : d107483 q = 1) : d110773 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7457, d110773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7457, d110773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7461 q = 1) (hb : d107483 q = 1) : d110777 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7461, d110777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16870 q ha hb
    | true =>
      simp only [d7461, d110777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16868 q ha hb
  have h6 (q : Pattern) (ha : d7462 q = 1) (hb : d107483 q = 1) : d110778 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7462, d110778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7462, d110778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7463 q = 1) (hb : d107483 q = 1) : d110779 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7463, d110779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7463, d110779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7472 q = 1) (hb : d107483 q = 1) : d110788 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7472, d110788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16872 q ha hb
    | true =>
      simp only [d7472, d110788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16862 q ha hb
  have h9 (q : Pattern) (ha : d85467 q = 1) (hb : d107483 q = 1) : d110789 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85467, d110789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85467, d110789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7487 q = 1) (hb : d107483 q = 1) : d110794 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7487, d110794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16873 q ha hb
    | true =>
      simp only [d7487, d110794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d7488 q = 1) (hb : d107483 q = 1) : d110795 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7488, d110795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7488, d110795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d85468 q = 1) (hb : d107483 q = 1) : d110796 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85468, d110796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85468, d110796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85469 q = 1) (hb : d107483 q = 1) : d110797 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85469, d110797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85469, d110797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85470 q = 1) (hb : d107483 q = 1) : d110798 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85470, d110798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85470, d110798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d7494 q = 1) (hb : d107483 q = 1) : d110801 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7494, d110801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16877 q ha hb
    | true =>
      simp only [d7494, d110801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16875 q ha hb
  have h16 (q : Pattern) (ha : d7495 q = 1) (hb : d107483 q = 1) : d110802 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7495, d110802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7495, d110802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d7496 q = 1) (hb : d107483 q = 1) : d110803 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7496, d110803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d7496, d110803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d7497 q = 1) (hb : d107483 q = 1) : d110804 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7497, d110804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7497, d110804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d7499 q = 1) (hb : d107483 q = 1) : d110806 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7499, d110806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16878 q ha hb
    | true =>
      simp only [d7499, d110806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16876 q ha hb
  have h20 (q : Pattern) (ha : d7500 q = 1) (hb : d107483 q = 1) : d110807 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7500, d110807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7500, d110807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d7501 q = 1) (hb : d107483 q = 1) : d110808 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7501, d110808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d7501, d110808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d7503 q = 1) (hb : d107483 q = 1) : d110810 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7503, d110810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16879 q ha hb
    | true =>
      simp only [d7503, d110810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16864 q ha hb
  have h23 (q : Pattern) (ha : d85472 q = 1) (hb : d107483 q = 1) : d110811 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85472, d110811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d85472, d110811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d7508 q = 1) (hb : d107483 q = 1) : d110813 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7508, d110813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16880 q ha hb
    | true =>
      simp only [d7508, d110813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d7509 q = 1) (hb : d107483 q = 1) : d110814 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7509, d110814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d7509, d110814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d85473 q = 1) (hb : d107483 q = 1) : d110815 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85473, d110815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d85473, d110815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d85474 q = 1) (hb : d107483 q = 1) : d110816 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85474, d110816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85474, d110816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d85475 q = 1) (hb : d107483 q = 1) : d110817 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85475, d110817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d85475, d110817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d85476 q = 1) (hb : d107483 q = 1) : d110818 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85476, d110818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85476, d110818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro16882 (p : Pattern) (ha : d85483 p = 1) (hb : d107483 p = 1) : d110827 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7503 q = 1) (hb : d107483 q = 1) : d110810 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7503, d110810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16879 q ha hb
    | true =>
      simp only [d7503, d110810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16864 q ha hb
  have h2 (q : Pattern) (ha : d85472 q = 1) (hb : d107483 q = 1) : d110811 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85472, d110811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85472, d110811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7508 q = 1) (hb : d107483 q = 1) : d110813 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7508, d110813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16880 q ha hb
    | true =>
      simp only [d7508, d110813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7509 q = 1) (hb : d107483 q = 1) : d110814 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7509, d110814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7509, d110814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85473 q = 1) (hb : d107483 q = 1) : d110815 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85473, d110815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85473, d110815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85481 q = 1) (hb : d107483 q = 1) : d110825 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85481, d110825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85481, d110825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85482 q = 1) (hb : d107483 q = 1) : d110826 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85482, d110826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85482, d110826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85483 q = 1) (hb : d107483 q = 1) : d110827 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85483, d110827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85483, d110827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16883 (p : Pattern) (ha : d7529 p = 1) (hb : d107483 p = 1) : d110834 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d664 q = 1) : d664 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d417 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d665 q = 1) (hb : d85721 q = 1) : d11013 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d665, d85721, d11013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d665, d85721, d11013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d666 q = 1) (hb : d85721 q = 1) : d11014 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d666, d11014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d666, d11014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d667 q = 1) (hb : d85721 q = 1) : d11015 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d667, d11015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d667, d11015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d417 q = 1) : d417 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d231 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d418 q = 1) (hb : d85721 q = 1) : d10814 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, d85721, d10814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d418, d85721, d10814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d419 q = 1) (hb : d85721 q = 1) : d10815 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, d10815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d419, d10815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d420 q = 1) (hb : d85721 q = 1) : d10816 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, d10816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d420, d10816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d668 q = 1) (hb : d85721 q = 1) : d11016 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d668, d11016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d668, d11016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7528 q = 1) (hb : d107483 q = 1) : d110833 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7528, d107483, d110833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7528, d107483, d110833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d7529 q = 1) (hb : d107483 q = 1) : d110834 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7529, d110834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d7529, d110834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro16884 (p : Pattern) (ha : d7535 p = 1) (hb : d107483 p = 1) : d110840 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7530 q = 1) (hb : d107483 q = 1) : d110835 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7530, d110835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16883 q ha hb
    | true =>
      simp only [d7530, d110835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7531 q = 1) (hb : d107483 q = 1) : d110836 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7531, d110836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7531, d110836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7391 q = 1) (hb : d107483 q = 1) : d110716 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7391, d110716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16848 q ha hb
    | true =>
      simp only [d7391, d110716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7392 q = 1) (hb : d107483 q = 1) : d110717 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7392, d110717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7392, d110717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7532 q = 1) (hb : d107483 q = 1) : d110837 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7532, d110837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7532, d110837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7533 q = 1) (hb : d107483 q = 1) : d110838 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7533, d110838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7533, d110838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7534 q = 1) (hb : d107483 q = 1) : d110839 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7534, d110839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7534, d110839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7535 q = 1) (hb : d107483 q = 1) : d110840 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7535, d110840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7535, d110840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro16885 (p : Pattern) (ha : d7539 p = 1) (hb : d107483 p = 1) : d110844 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7391 q = 1) (hb : d107483 q = 1) : d110716 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7391, d110716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16848 q ha hb
    | true =>
      simp only [d7391, d110716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7392 q = 1) (hb : d107483 q = 1) : d110717 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7392, d110717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7392, d110717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d684 q = 1) (hb : d107483 q = 1) : d11032 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d11032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16859 q ha hb
    | true =>
      simp only [d684, d11032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d685 q = 1) (hb : d107483 q = 1) : d11033 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d11033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d11033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7536 q = 1) (hb : d107483 q = 1) : d110841 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7536, d110841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7536, d110841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7537 q = 1) (hb : d107483 q = 1) : d110842 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7537, d110842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7537, d110842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7538 q = 1) (hb : d107483 q = 1) : d110843 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7538, d110843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7538, d110843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7539 q = 1) (hb : d107483 q = 1) : d110844 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7539, d110844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7539, d110844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro16886 (p : Pattern) (ha : d7554 p = 1) (hb : d107483 p = 1) : d110850 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7391 q = 1) (hb : d107483 q = 1) : d110716 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7391, d110716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16848 q ha hb
    | true =>
      simp only [d7391, d110716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7392 q = 1) (hb : d107483 q = 1) : d110717 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7392, d110717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7392, d110717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7551 q = 1) (hb : d107483 q = 1) : d110847 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7551, d110847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7551, d110847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7552 q = 1) (hb : d107483 q = 1) : d110848 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7552, d110848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7552, d110848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7553 q = 1) (hb : d107483 q = 1) : d110849 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7553, d110849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7553, d110849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7554 q = 1) (hb : d107483 q = 1) : d110850 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7554, d110850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7554, d110850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16887 (p : Pattern) (ha : d85493 p = 1) (hb : d107483 p = 1) : d110856 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7540 q = 1) (hb : d107483 q = 1) : d110845 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7540, d110845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16884 q ha hb
    | true =>
      simp only [d7540, d110845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16885 q ha hb
  have h2 (q : Pattern) (ha : d85489 q = 1) (hb : d107483 q = 1) : d110846 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85489, d110846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85489, d110846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7555 q = 1) (hb : d107483 q = 1) : d110851 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7555, d110851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16886 q ha hb
    | true =>
      simp only [d7555, d110851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7556 q = 1) (hb : d107483 q = 1) : d110852 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7556, d110852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7556, d110852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85490 q = 1) (hb : d107483 q = 1) : d110853 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85490, d110853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85490, d110853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85491 q = 1) (hb : d107483 q = 1) : d110854 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85491, d110854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85491, d110854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85492 q = 1) (hb : d107483 q = 1) : d110855 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85492, d110855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85492, d110855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85493 q = 1) (hb : d107483 q = 1) : d110856 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85493, d110856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85493, d110856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16888 (p : Pattern) (ha : d85499 p = 1) (hb : d107483 p = 1) : d110862 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7440 q = 1) (hb : d107483 q = 1) : d110756 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7440, d110756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7440, d110756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16863 q ha hb
  have h2 (q : Pattern) (ha : d7441 q = 1) (hb : d107483 q = 1) : d110757 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7441, d110757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7441, d110757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7449 q = 1) (hb : d107483 q = 1) : d110765 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7449, d110765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16863 q ha hb
    | true =>
      simp only [d7449, d110765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16865 q ha hb
  have h4 (q : Pattern) (ha : d7450 q = 1) (hb : d107483 q = 1) : d110766 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7450, d110766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7450, d110766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7451 q = 1) (hb : d107483 q = 1) : d110767 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7451, d110767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7451, d110767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85477 q = 1) (hb : d107483 q = 1) : d110819 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85477, d110819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16874 q ha hb
    | true =>
      simp only [d85477, d110819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16881 q ha hb
  have h7 (q : Pattern) (ha : d7516 q = 1) (hb : d107483 q = 1) : d110821 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7516, d110821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16866 q ha hb
    | true =>
      simp only [d7516, d110821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16857 q ha hb
  have h8 (q : Pattern) (ha : d85478 q = 1) (hb : d107483 q = 1) : d110822 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85478, d110822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85478, d110822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85479 q = 1) (hb : d107483 q = 1) : d110823 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85479, d110823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85479, d110823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d85480 q = 1) (hb : d107483 q = 1) : d110824 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85480, d110824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85480, d110824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d85484 q = 1) (hb : d107483 q = 1) : d110828 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85484, d110828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85484, d110828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16882 q ha hb
  have h12 (q : Pattern) (ha : d654 q = 1) (hb : d107483 q = 1) : d11008 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, d11008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d654, d11008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16858 q ha hb
  have h13 (q : Pattern) (ha : d85485 q = 1) (hb : d107483 q = 1) : d110829 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85485, d110829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85485, d110829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85486 q = 1) (hb : d107483 q = 1) : d110830 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85486, d110830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85486, d110830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d85487 q = 1) (hb : d107483 q = 1) : d110831 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85487, d110831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85487, d110831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d85488 q = 1) (hb : d107483 q = 1) : d110832 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85488, d110832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85488, d110832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85494 q = 1) (hb : d107483 q = 1) : d110857 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85494, d110857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85494, d110857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16887 q ha hb
  have h18 (q : Pattern) (ha : d737 q = 1) (hb : d107483 q = 1) : d11083 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, d11083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d737, d11083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16861 q ha hb
  have h19 (q : Pattern) (ha : d85495 q = 1) (hb : d107483 q = 1) : d110858 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85495, d110858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85495, d110858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d85496 q = 1) (hb : d107483 q = 1) : d110859 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85496, d110859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d85496, d110859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d85497 q = 1) (hb : d107483 q = 1) : d110860 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85497, d110860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d85497, d110860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d85498 q = 1) (hb : d107483 q = 1) : d110861 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85498, d110861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85498, d110861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d85499 q = 1) (hb : d107483 q = 1) : d110862 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85499, d110862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85499, d110862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro16889 (p : Pattern) (ha : d85505 p = 1) (hb : d107483 p = 1) : d110868 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85500 q = 1) (hb : d107483 q = 1) : d110863 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85500, d110863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85500, d110863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16888 q ha hb
  have h2 (q : Pattern) (ha : d85501 q = 1) (hb : d107483 q = 1) : d110864 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85501, d110864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85501, d110864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85502 q = 1) (hb : d107483 q = 1) : d110865 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85502, d110865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85502, d110865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85503 q = 1) (hb : d107483 q = 1) : d110866 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85503, d110866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85503, d110866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85504 q = 1) (hb : d107483 q = 1) : d110867 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85504, d110867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85504, d110867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85505 q = 1) (hb : d107483 q = 1) : d110868 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85505, d110868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85505, d110868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16890 (p : Pattern) (ha : d773 p = 1) (hb : d107483 p = 1) : d11109 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d758 q = 1) : d758 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d762 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d763 q = 1) (hb : d85721 q = 1) : d11099 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d85721, d11099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d763, d85721, d11099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d764 q = 1) (hb : d85721 q = 1) : d11100 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d11100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d11100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d765 q = 1) (hb : d85721 q = 1) : d11101 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d11101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d11101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d767 q = 1) (hb : d85721 q = 1) : d11103 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d11103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d767, d11103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d772 q = 1) (hb : d107483 q = 1) : d11108 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d772, d107483, d11108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d772, d107483, d11108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d773 q = 1) (hb : d107483 q = 1) : d11109 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d773, d11109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d773, d11109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro16891 (p : Pattern) (ha : d783 p = 1) (hb : d107483 p = 1) : d11119 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d107483 q = 1) : d11110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16890 q ha hb
    | true =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d107483 q = 1) : d11111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d107483 q = 1) : d11116 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d11116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d11116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d107483 q = 1) : d11117 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d11117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d11117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d107483 q = 1) : d11118 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d11118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, d11118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d783 q = 1) (hb : d107483 q = 1) : d11119 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d783, d11119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d783, d11119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16892 (p : Pattern) (ha : d793 p = 1) (hb : d107483 p = 1) : d11129 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d107483 q = 1) : d11110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16890 q ha hb
    | true =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d107483 q = 1) : d11111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d107483 q = 1) : d11116 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d11116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d11116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d107483 q = 1) : d11117 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d11117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d11117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d107483 q = 1) : d11118 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d11118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, d11118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d793 q = 1) (hb : d107483 q = 1) : d11129 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d793, d11129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d793, d11129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16893 (p : Pattern) (ha : d950 p = 1) (hb : d107483 p = 1) : d11249 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d939 q = 1) (hb : d107483 q = 1) : d11238 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d11238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16891 q ha hb
    | true =>
      simp only [d939, d11238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d940 q = 1) (hb : d107483 q = 1) : d11239 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d11239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d11239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d941 q = 1) (hb : d107483 q = 1) : d11240 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d11240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d941, d11240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d942 q = 1) (hb : d107483 q = 1) : d11241 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d11241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d11241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d943 q = 1) (hb : d107483 q = 1) : d11242 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d11242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d11242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d945 q = 1) (hb : d107483 q = 1) : d11244 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d11244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16892 q ha hb
    | true =>
      simp only [d945, d11244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d946 q = 1) (hb : d107483 q = 1) : d11245 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d11245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, d11245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d947 q = 1) (hb : d107483 q = 1) : d11246 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d11246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d947, d11246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d948 q = 1) (hb : d107483 q = 1) : d11247 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d11247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, d11247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d949 q = 1) (hb : d107483 q = 1) : d11248 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d11248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, d11248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d950 q = 1) (hb : d107483 q = 1) : d11249 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d950, d11249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d950, d11249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro16894 (p : Pattern) (ha : d959 p = 1) (hb : d107483 p = 1) : d11258 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d945 q = 1) (hb : d107483 q = 1) : d11244 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d11244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16892 q ha hb
    | true =>
      simp only [d945, d11244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d946 q = 1) (hb : d107483 q = 1) : d11245 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d11245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, d11245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d947 q = 1) (hb : d107483 q = 1) : d11246 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d11246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d947, d11246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d948 q = 1) (hb : d107483 q = 1) : d11247 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d11247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, d11247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d949 q = 1) (hb : d107483 q = 1) : d11248 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d11248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, d11248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d959 q = 1) (hb : d107483 q = 1) : d11258 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d959, d11258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d959, d11258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16895 (p : Pattern) (ha : d1005 p = 1) (hb : d107483 p = 1) : d11289 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d981 q = 1) : d981 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d986 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d987 q = 1) (hb : d85721 q = 1) : d11271 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d85721, d11271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d987, d85721, d11271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d988 q = 1) (hb : d85721 q = 1) : d11272 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d11272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d11272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d989 q = 1) (hb : d85721 q = 1) : d11273 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d11273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d11273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d995 q = 1) (hb : d85721 q = 1) : d11279 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d11279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d995, d11279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1004 q = 1) (hb : d107483 q = 1) : d11288 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1004, d107483, d11288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1004, d107483, d11288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1005 q = 1) (hb : d107483 q = 1) : d11289 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1005, d11289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1005, d11289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro16896 (p : Pattern) (ha : d1063 p = 1) (hb : d107483 p = 1) : d11345 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1006 q = 1) (hb : d107483 q = 1) : d11290 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d11290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16895 q ha hb
    | true =>
      simp only [d1006, d11290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1007 q = 1) (hb : d107483 q = 1) : d11291 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d11291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d11291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1060 q = 1) (hb : d107483 q = 1) : d11342 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1060, d11342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1060, d11342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1061 q = 1) (hb : d107483 q = 1) : d11343 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1061, d11343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1061, d11343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1062 q = 1) (hb : d107483 q = 1) : d11344 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1062, d11344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1062, d11344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1063 q = 1) (hb : d107483 q = 1) : d11345 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1063, d11345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1063, d11345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16897 (p : Pattern) (ha : d1069 p = 1) (hb : d107483 p = 1) : d11351 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1064 q = 1) (hb : d107483 q = 1) : d11346 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1064, d11346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16896 q ha hb
    | true =>
      simp only [d1064, d11346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1065 q = 1) (hb : d107483 q = 1) : d11347 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1065, d11347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1065, d11347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1066 q = 1) (hb : d107483 q = 1) : d11348 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1066, d11348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1066, d11348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1067 q = 1) (hb : d107483 q = 1) : d11349 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1067, d11349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1067, d11349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1068 q = 1) (hb : d107483 q = 1) : d11350 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1068, d11350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1068, d11350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1069 q = 1) (hb : d107483 q = 1) : d11351 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1069, d11351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1069, d11351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16898 (p : Pattern) (ha : d7575 p = 1) (hb : d107483 p = 1) : d110871 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d756 q = 1) : d756 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d758 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d759 q = 1) (hb : d85721 q = 1) : d11096 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d759, d85721, d11096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d759, d85721, d11096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d760 q = 1) (hb : d85721 q = 1) : d11097 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d760, d11097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d760, d11097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d761 q = 1) (hb : d85721 q = 1) : d11098 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d761, d11098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d761, d11098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d758 q = 1) : d758 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d762 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d763 q = 1) (hb : d85721 q = 1) : d11099 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d85721, d11099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d763, d85721, d11099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d764 q = 1) (hb : d85721 q = 1) : d11100 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d11100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d11100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d765 q = 1) (hb : d85721 q = 1) : d11101 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d11101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d11101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d766 q = 1) (hb : d85721 q = 1) : d11102 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d766, d11102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d766, d11102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7574 q = 1) (hb : d107483 q = 1) : d110870 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7574, d107483, d110870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7574, d107483, d110870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d7575 q = 1) (hb : d107483 q = 1) : d110871 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7575, d110871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d7575, d110871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro16899 (p : Pattern) (ha : d7581 p = 1) (hb : d107483 p = 1) : d110877 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7576 q = 1) (hb : d107483 q = 1) : d110872 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16898 q ha hb
    | true =>
      simp only [d7576, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7577 q = 1) (hb : d107483 q = 1) : d110873 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d107483 q = 1) : d11110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16890 q ha hb
    | true =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d107483 q = 1) : d11111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7578 q = 1) (hb : d107483 q = 1) : d110874 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7578, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7579 q = 1) (hb : d107483 q = 1) : d110875 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7579, d110875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7579, d110875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7580 q = 1) (hb : d107483 q = 1) : d110876 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7580, d110876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7580, d110876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7581 q = 1) (hb : d107483 q = 1) : d110877 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7581, d110877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7581, d110877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16900 (p : Pattern) (ha : d7587 p = 1) (hb : d107483 p = 1) : d110883 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7582 q = 1) (hb : d107483 q = 1) : d110878 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7582, d110878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16899 q ha hb
    | true =>
      simp only [d7582, d110878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16891 q ha hb
  have h2 (q : Pattern) (ha : d7583 q = 1) (hb : d107483 q = 1) : d110879 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7583, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7583, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7584 q = 1) (hb : d107483 q = 1) : d110880 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7584, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7584, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7585 q = 1) (hb : d107483 q = 1) : d110881 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7585, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7585, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7586 q = 1) (hb : d107483 q = 1) : d110882 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7586, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7586, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7587 q = 1) (hb : d107483 q = 1) : d110883 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7587, d110883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7587, d110883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16901 (p : Pattern) (ha : d7590 p = 1) (hb : d107483 p = 1) : d110886 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7576 q = 1) (hb : d107483 q = 1) : d110872 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16898 q ha hb
    | true =>
      simp only [d7576, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7577 q = 1) (hb : d107483 q = 1) : d110873 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d107483 q = 1) : d11110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16890 q ha hb
    | true =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d107483 q = 1) : d11111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7578 q = 1) (hb : d107483 q = 1) : d110874 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7578, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7579 q = 1) (hb : d107483 q = 1) : d110875 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7579, d110875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7579, d110875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7580 q = 1) (hb : d107483 q = 1) : d110876 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7580, d110876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7580, d110876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7590 q = 1) (hb : d107483 q = 1) : d110886 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7590, d110886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7590, d110886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro16902 (p : Pattern) (ha : d7596 p = 1) (hb : d107483 p = 1) : d110892 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7582 q = 1) (hb : d107483 q = 1) : d110878 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7582, d110878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16899 q ha hb
    | true =>
      simp only [d7582, d110878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16891 q ha hb
  have h2 (q : Pattern) (ha : d7583 q = 1) (hb : d107483 q = 1) : d110879 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7583, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7583, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7584 q = 1) (hb : d107483 q = 1) : d110880 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7584, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7584, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7585 q = 1) (hb : d107483 q = 1) : d110881 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7585, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7585, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7586 q = 1) (hb : d107483 q = 1) : d110882 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7586, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7586, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7591 q = 1) (hb : d107483 q = 1) : d110887 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7591, d110887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16901 q ha hb
    | true =>
      simp only [d7591, d110887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16892 q ha hb
  have h7 (q : Pattern) (ha : d7592 q = 1) (hb : d107483 q = 1) : d110888 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7592, d110888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7592, d110888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7593 q = 1) (hb : d107483 q = 1) : d110889 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7593, d110889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7593, d110889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d7594 q = 1) (hb : d107483 q = 1) : d110890 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7594, d110890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7594, d110890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7595 q = 1) (hb : d107483 q = 1) : d110891 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7595, d110891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7595, d110891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7596 q = 1) (hb : d107483 q = 1) : d110892 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7596, d110892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7596, d110892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro16903 (p : Pattern) (ha : d7663 p = 1) (hb : d107483 p = 1) : d110948 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7582 q = 1) (hb : d107483 q = 1) : d110878 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7582, d110878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16899 q ha hb
    | true =>
      simp only [d7582, d110878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16891 q ha hb
  have h2 (q : Pattern) (ha : d7583 q = 1) (hb : d107483 q = 1) : d110879 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7583, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7583, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7584 q = 1) (hb : d107483 q = 1) : d110880 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7584, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7584, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7585 q = 1) (hb : d107483 q = 1) : d110881 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7585, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7585, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7586 q = 1) (hb : d107483 q = 1) : d110882 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7586, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7586, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d939 q = 1) (hb : d107483 q = 1) : d11238 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d11238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16891 q ha hb
    | true =>
      simp only [d939, d11238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d940 q = 1) (hb : d107483 q = 1) : d11239 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d11239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d11239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d941 q = 1) (hb : d107483 q = 1) : d11240 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d11240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d941, d11240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d942 q = 1) (hb : d107483 q = 1) : d11241 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d11241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d11241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d943 q = 1) (hb : d107483 q = 1) : d11242 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d11242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d11242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7663 q = 1) (hb : d107483 q = 1) : d110948 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7663, d110948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7663, d110948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro16904 (p : Pattern) (ha : d806 p = 1) (hb : d107483 p = 1) : d11142 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d107483 q = 1) : d11110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16890 q ha hb
    | true =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d107483 q = 1) : d11111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d107483 q = 1) : d11116 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d11116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d11116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d107483 q = 1) : d11117 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d11117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d11117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d107483 q = 1) : d11141 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d11141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d11141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d806 q = 1) (hb : d107483 q = 1) : d11142 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d806, d11142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d806, d11142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16905 (p : Pattern) (ha : d816 p = 1) (hb : d107483 p = 1) : d11152 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d107483 q = 1) : d11110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16890 q ha hb
    | true =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d107483 q = 1) : d11111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d107483 q = 1) : d11116 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d11116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d11116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d107483 q = 1) : d11150 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d11150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d11150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d107483 q = 1) : d11151 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d11151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, d11151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d816 q = 1) (hb : d107483 q = 1) : d11152 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d816, d11152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d816, d11152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16906 (p : Pattern) (ha : d7601 p = 1) (hb : d107483 p = 1) : d110897 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7576 q = 1) (hb : d107483 q = 1) : d110872 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16898 q ha hb
    | true =>
      simp only [d7576, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7577 q = 1) (hb : d107483 q = 1) : d110873 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d107483 q = 1) : d11110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16890 q ha hb
    | true =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d107483 q = 1) : d11111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7578 q = 1) (hb : d107483 q = 1) : d110874 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7578, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7579 q = 1) (hb : d107483 q = 1) : d110875 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7579, d110875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7579, d110875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7600 q = 1) (hb : d107483 q = 1) : d110896 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7600, d110896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7600, d110896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7601 q = 1) (hb : d107483 q = 1) : d110897 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7601, d110897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7601, d110897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16907 (p : Pattern) (ha : d7608 p = 1) (hb : d107483 p = 1) : d110904 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7576 q = 1) (hb : d107483 q = 1) : d110872 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16898 q ha hb
    | true =>
      simp only [d7576, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7577 q = 1) (hb : d107483 q = 1) : d110873 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d107483 q = 1) : d11110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16890 q ha hb
    | true =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d107483 q = 1) : d11111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7578 q = 1) (hb : d107483 q = 1) : d110874 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7578, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7606 q = 1) (hb : d107483 q = 1) : d110902 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7606, d110902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7606, d110902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7607 q = 1) (hb : d107483 q = 1) : d110903 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7607, d110903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7607, d110903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7608 q = 1) (hb : d107483 q = 1) : d110904 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7608, d110904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7608, d110904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16908 (p : Pattern) (ha : d7613 p = 1) (hb : d107483 p = 1) : d110909 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d839 q = 1) : d839 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d756 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d840 q = 1) (hb : d85721 q = 1) : d11156 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d840, d85721, d11156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d840, d85721, d11156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d841 q = 1) (hb : d85721 q = 1) : d11157 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d841, d11157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d841, d11157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d842 q = 1) (hb : d85721 q = 1) : d11158 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d842, d11158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d842, d11158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d756 q = 1) : d756 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d758 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d759 q = 1) (hb : d85721 q = 1) : d11096 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d759, d85721, d11096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d759, d85721, d11096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d760 q = 1) (hb : d85721 q = 1) : d11097 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d760, d11097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d760, d11097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d761 q = 1) (hb : d85721 q = 1) : d11098 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d761, d11098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d761, d11098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d843 q = 1) (hb : d85721 q = 1) : d11159 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d843, d11159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d843, d11159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7612 q = 1) (hb : d107483 q = 1) : d110908 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7612, d107483, d110908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7612, d107483, d110908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d7613 q = 1) (hb : d107483 q = 1) : d110909 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7613, d110909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d7613, d110909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro16909 (p : Pattern) (ha : d7619 p = 1) (hb : d107483 p = 1) : d110915 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7614 q = 1) (hb : d107483 q = 1) : d110910 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7614, d110910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16908 q ha hb
    | true =>
      simp only [d7614, d110910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7615 q = 1) (hb : d107483 q = 1) : d110911 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7615, d110911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7615, d110911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7576 q = 1) (hb : d107483 q = 1) : d110872 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16898 q ha hb
    | true =>
      simp only [d7576, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7577 q = 1) (hb : d107483 q = 1) : d110873 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7616 q = 1) (hb : d107483 q = 1) : d110912 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7616, d110912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7616, d110912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7617 q = 1) (hb : d107483 q = 1) : d110913 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7617, d110913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7617, d110913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7618 q = 1) (hb : d107483 q = 1) : d110914 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7618, d110914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7618, d110914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7619 q = 1) (hb : d107483 q = 1) : d110915 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7619, d110915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7619, d110915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16910 (p : Pattern) (ha : d7634 p = 1) (hb : d107483 p = 1) : d110921 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7576 q = 1) (hb : d107483 q = 1) : d110872 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16898 q ha hb
    | true =>
      simp only [d7576, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7577 q = 1) (hb : d107483 q = 1) : d110873 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7631 q = 1) (hb : d107483 q = 1) : d110918 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7631, d110918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7631, d110918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7632 q = 1) (hb : d107483 q = 1) : d110919 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7632, d110919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7632, d110919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7633 q = 1) (hb : d107483 q = 1) : d110920 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7633, d110920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7633, d110920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7634 q = 1) (hb : d107483 q = 1) : d110921 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7634, d110921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7634, d110921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16911 (p : Pattern) (ha : d85511 p = 1) (hb : d107483 p = 1) : d110927 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7602 q = 1) (hb : d107483 q = 1) : d110898 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7602, d110898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16906 q ha hb
    | true =>
      simp only [d7602, d110898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16904 q ha hb
  have h2 (q : Pattern) (ha : d7603 q = 1) (hb : d107483 q = 1) : d110899 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7603, d110899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7603, d110899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7604 q = 1) (hb : d107483 q = 1) : d110900 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7604, d110900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7604, d110900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7605 q = 1) (hb : d107483 q = 1) : d110901 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7605, d110901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7605, d110901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7609 q = 1) (hb : d107483 q = 1) : d110905 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7609, d110905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16907 q ha hb
    | true =>
      simp only [d7609, d110905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16905 q ha hb
  have h6 (q : Pattern) (ha : d7610 q = 1) (hb : d107483 q = 1) : d110906 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7610, d110906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7610, d110906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7611 q = 1) (hb : d107483 q = 1) : d110907 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7611, d110907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7611, d110907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7620 q = 1) (hb : d107483 q = 1) : d110916 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7620, d110916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16909 q ha hb
    | true =>
      simp only [d7620, d110916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16899 q ha hb
  have h9 (q : Pattern) (ha : d85507 q = 1) (hb : d107483 q = 1) : d110917 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85507, d110917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85507, d110917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7635 q = 1) (hb : d107483 q = 1) : d110922 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7635, d110922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16910 q ha hb
    | true =>
      simp only [d7635, d110922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d7636 q = 1) (hb : d107483 q = 1) : d110923 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7636, d110923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7636, d110923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d85508 q = 1) (hb : d107483 q = 1) : d110924 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85508, d110924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85508, d110924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85509 q = 1) (hb : d107483 q = 1) : d110925 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85509, d110925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85509, d110925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85510 q = 1) (hb : d107483 q = 1) : d110926 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85510, d110926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85510, d110926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85511 q = 1) (hb : d107483 q = 1) : d110927 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85511, d110927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85511, d110927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro16912 (p : Pattern) (ha : d916 p = 1) (hb : d107483 p = 1) : d11214 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d107483 q = 1) : d11110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16890 q ha hb
    | true =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d107483 q = 1) : d11111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d107483 q = 1) : d11116 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d11116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d11116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d107483 q = 1) : d11117 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d11117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d11117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d107483 q = 1) : d11141 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d11141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d11141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d916 q = 1) (hb : d107483 q = 1) : d11214 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d916, d11214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d916, d11214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16913 (p : Pattern) (ha : d922 p = 1) (hb : d107483 p = 1) : d11220 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d107483 q = 1) : d11110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16890 q ha hb
    | true =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d107483 q = 1) : d11111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d107483 q = 1) : d11116 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d11116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d11116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d107483 q = 1) : d11150 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d11150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d11150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d107483 q = 1) : d11151 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d11151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, d11151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d922 q = 1) (hb : d107483 q = 1) : d11220 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d922, d11220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d922, d11220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16914 (p : Pattern) (ha : d7641 p = 1) (hb : d107483 p = 1) : d110928 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7576 q = 1) (hb : d107483 q = 1) : d110872 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16898 q ha hb
    | true =>
      simp only [d7576, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7577 q = 1) (hb : d107483 q = 1) : d110873 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d107483 q = 1) : d11110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16890 q ha hb
    | true =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d107483 q = 1) : d11111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7578 q = 1) (hb : d107483 q = 1) : d110874 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7578, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7579 q = 1) (hb : d107483 q = 1) : d110875 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7579, d110875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7579, d110875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7600 q = 1) (hb : d107483 q = 1) : d110896 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7600, d110896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7600, d110896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7641 q = 1) (hb : d107483 q = 1) : d110928 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7641, d110928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7641, d110928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro16915 (p : Pattern) (ha : d7646 p = 1) (hb : d107483 p = 1) : d110933 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7576 q = 1) (hb : d107483 q = 1) : d110872 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16898 q ha hb
    | true =>
      simp only [d7576, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7577 q = 1) (hb : d107483 q = 1) : d110873 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d107483 q = 1) : d11110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16890 q ha hb
    | true =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d107483 q = 1) : d11111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7578 q = 1) (hb : d107483 q = 1) : d110874 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7578, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7606 q = 1) (hb : d107483 q = 1) : d110902 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7606, d110902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7606, d110902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7607 q = 1) (hb : d107483 q = 1) : d110903 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7607, d110903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7607, d110903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7646 q = 1) (hb : d107483 q = 1) : d110933 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7646, d110933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7646, d110933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro16916 (p : Pattern) (ha : d7650 p = 1) (hb : d107483 p = 1) : d110937 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7614 q = 1) (hb : d107483 q = 1) : d110910 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7614, d110910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16908 q ha hb
    | true =>
      simp only [d7614, d110910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7615 q = 1) (hb : d107483 q = 1) : d110911 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7615, d110911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7615, d110911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7576 q = 1) (hb : d107483 q = 1) : d110872 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16898 q ha hb
    | true =>
      simp only [d7576, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7577 q = 1) (hb : d107483 q = 1) : d110873 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7616 q = 1) (hb : d107483 q = 1) : d110912 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7616, d110912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7616, d110912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7617 q = 1) (hb : d107483 q = 1) : d110913 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7617, d110913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7617, d110913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7618 q = 1) (hb : d107483 q = 1) : d110914 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7618, d110914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7618, d110914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7650 q = 1) (hb : d107483 q = 1) : d110937 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7650, d110937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7650, d110937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro16917 (p : Pattern) (ha : d7655 p = 1) (hb : d107483 p = 1) : d110940 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7576 q = 1) (hb : d107483 q = 1) : d110872 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16898 q ha hb
    | true =>
      simp only [d7576, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7577 q = 1) (hb : d107483 q = 1) : d110873 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7631 q = 1) (hb : d107483 q = 1) : d110918 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7631, d110918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7631, d110918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7632 q = 1) (hb : d107483 q = 1) : d110919 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7632, d110919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7632, d110919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7633 q = 1) (hb : d107483 q = 1) : d110920 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7633, d110920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7633, d110920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7655 q = 1) (hb : d107483 q = 1) : d110940 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7655, d110940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7655, d110940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16918 (p : Pattern) (ha : d85516 p = 1) (hb : d107483 p = 1) : d110946 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7602 q = 1) (hb : d107483 q = 1) : d110898 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7602, d110898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16906 q ha hb
    | true =>
      simp only [d7602, d110898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16904 q ha hb
  have h2 (q : Pattern) (ha : d7603 q = 1) (hb : d107483 q = 1) : d110899 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7603, d110899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7603, d110899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7604 q = 1) (hb : d107483 q = 1) : d110900 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7604, d110900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7604, d110900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7605 q = 1) (hb : d107483 q = 1) : d110901 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7605, d110901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7605, d110901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7609 q = 1) (hb : d107483 q = 1) : d110905 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7609, d110905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16907 q ha hb
    | true =>
      simp only [d7609, d110905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16905 q ha hb
  have h6 (q : Pattern) (ha : d7610 q = 1) (hb : d107483 q = 1) : d110906 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7610, d110906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7610, d110906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7611 q = 1) (hb : d107483 q = 1) : d110907 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7611, d110907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7611, d110907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7620 q = 1) (hb : d107483 q = 1) : d110916 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7620, d110916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16909 q ha hb
    | true =>
      simp only [d7620, d110916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16899 q ha hb
  have h9 (q : Pattern) (ha : d85507 q = 1) (hb : d107483 q = 1) : d110917 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85507, d110917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85507, d110917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7635 q = 1) (hb : d107483 q = 1) : d110922 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7635, d110922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16910 q ha hb
    | true =>
      simp only [d7635, d110922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d7636 q = 1) (hb : d107483 q = 1) : d110923 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7636, d110923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7636, d110923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d85508 q = 1) (hb : d107483 q = 1) : d110924 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85508, d110924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85508, d110924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85509 q = 1) (hb : d107483 q = 1) : d110925 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85509, d110925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85509, d110925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85510 q = 1) (hb : d107483 q = 1) : d110926 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85510, d110926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85510, d110926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d7642 q = 1) (hb : d107483 q = 1) : d110929 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7642, d110929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16914 q ha hb
    | true =>
      simp only [d7642, d110929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16912 q ha hb
  have h16 (q : Pattern) (ha : d7643 q = 1) (hb : d107483 q = 1) : d110930 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7643, d110930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7643, d110930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d7644 q = 1) (hb : d107483 q = 1) : d110931 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7644, d110931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d7644, d110931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d7645 q = 1) (hb : d107483 q = 1) : d110932 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7645, d110932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7645, d110932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d7647 q = 1) (hb : d107483 q = 1) : d110934 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7647, d110934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16915 q ha hb
    | true =>
      simp only [d7647, d110934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16913 q ha hb
  have h20 (q : Pattern) (ha : d7648 q = 1) (hb : d107483 q = 1) : d110935 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7648, d110935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7648, d110935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d7649 q = 1) (hb : d107483 q = 1) : d110936 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7649, d110936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d7649, d110936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d7651 q = 1) (hb : d107483 q = 1) : d110938 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7651, d110938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16916 q ha hb
    | true =>
      simp only [d7651, d110938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16901 q ha hb
  have h23 (q : Pattern) (ha : d85512 q = 1) (hb : d107483 q = 1) : d110939 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85512, d110939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d85512, d110939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d7656 q = 1) (hb : d107483 q = 1) : d110941 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7656, d110941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16917 q ha hb
    | true =>
      simp only [d7656, d110941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d7657 q = 1) (hb : d107483 q = 1) : d110942 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7657, d110942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d7657, d110942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d85513 q = 1) (hb : d107483 q = 1) : d110943 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85513, d110943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d85513, d110943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d85514 q = 1) (hb : d107483 q = 1) : d110944 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85514, d110944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85514, d110944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d85515 q = 1) (hb : d107483 q = 1) : d110945 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85515, d110945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d85515, d110945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d85516 q = 1) (hb : d107483 q = 1) : d110946 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85516, d110946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85516, d110946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro16919 (p : Pattern) (ha : d85523 p = 1) (hb : d107483 p = 1) : d110955 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7651 q = 1) (hb : d107483 q = 1) : d110938 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7651, d110938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16916 q ha hb
    | true =>
      simp only [d7651, d110938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16901 q ha hb
  have h2 (q : Pattern) (ha : d85512 q = 1) (hb : d107483 q = 1) : d110939 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85512, d110939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85512, d110939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7656 q = 1) (hb : d107483 q = 1) : d110941 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7656, d110941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16917 q ha hb
    | true =>
      simp only [d7656, d110941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7657 q = 1) (hb : d107483 q = 1) : d110942 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7657, d110942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7657, d110942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85513 q = 1) (hb : d107483 q = 1) : d110943 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85513, d110943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85513, d110943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85521 q = 1) (hb : d107483 q = 1) : d110953 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85521, d110953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85521, d110953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85522 q = 1) (hb : d107483 q = 1) : d110954 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85522, d110954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85522, d110954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85523 q = 1) (hb : d107483 q = 1) : d110955 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85523, d110955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85523, d110955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16920 (p : Pattern) (ha : d7677 p = 1) (hb : d107483 p = 1) : d110962 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d970 q = 1) : d970 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d976 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d977 q = 1) (hb : d85721 q = 1) : d11264 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d977, d85721, d11264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d977, d85721, d11264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d978 q = 1) (hb : d85721 q = 1) : d11265 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d978, d11265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d978, d11265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d979 q = 1) (hb : d85721 q = 1) : d11266 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d979, d11266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d979, d11266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d976 q = 1) : d976 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d981 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d982 q = 1) (hb : d85721 q = 1) : d11267 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d982, d85721, d11267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d982, d85721, d11267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d983 q = 1) (hb : d85721 q = 1) : d11268 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d983, d11268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d983, d11268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d984 q = 1) (hb : d85721 q = 1) : d11269 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d984, d11269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d984, d11269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d985 q = 1) (hb : d85721 q = 1) : d11270 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d985, d11270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d985, d11270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7676 q = 1) (hb : d107483 q = 1) : d110961 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7676, d107483, d110961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7676, d107483, d110961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d7677 q = 1) (hb : d107483 q = 1) : d110962 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7677, d110962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d7677, d110962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro16921 (p : Pattern) (ha : d7681 p = 1) (hb : d107483 p = 1) : d110966 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d976 q = 1) : d976 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d981 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d982 q = 1) (hb : d85721 q = 1) : d11267 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d982, d85721, d11267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d982, d85721, d11267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d983 q = 1) (hb : d85721 q = 1) : d11268 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d983, d11268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d983, d11268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d984 q = 1) (hb : d85721 q = 1) : d11269 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d984, d11269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d984, d11269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d981 q = 1) : d981 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d986 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d987 q = 1) (hb : d85721 q = 1) : d11271 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d85721, d11271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d987, d85721, d11271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d988 q = 1) (hb : d85721 q = 1) : d11272 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d11272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d11272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d989 q = 1) (hb : d85721 q = 1) : d11273 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d11273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d11273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d990 q = 1) (hb : d85721 q = 1) : d11274 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d990, d11274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d990, d11274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7680 q = 1) (hb : d107483 q = 1) : d110965 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7680, d107483, d110965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7680, d107483, d110965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d7681 q = 1) (hb : d107483 q = 1) : d110966 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7681, d110966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d7681, d110966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro16922 (p : Pattern) (ha : d7687 p = 1) (hb : d107483 p = 1) : d110972 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7678 q = 1) (hb : d107483 q = 1) : d110963 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7678, d110963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16920 q ha hb
    | true =>
      simp only [d7678, d110963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7679 q = 1) (hb : d107483 q = 1) : d110964 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7679, d110964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7679, d110964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7682 q = 1) (hb : d107483 q = 1) : d110967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7682, d110967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16921 q ha hb
    | true =>
      simp only [d7682, d110967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7683 q = 1) (hb : d107483 q = 1) : d110968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7683, d110968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7683, d110968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7684 q = 1) (hb : d107483 q = 1) : d110969 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7684, d110969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7684, d110969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7685 q = 1) (hb : d107483 q = 1) : d110970 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7685, d110970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7685, d110970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7686 q = 1) (hb : d107483 q = 1) : d110971 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7686, d110971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7686, d110971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7687 q = 1) (hb : d107483 q = 1) : d110972 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7687, d110972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7687, d110972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro16923 (p : Pattern) (ha : d7691 p = 1) (hb : d107483 p = 1) : d110976 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7682 q = 1) (hb : d107483 q = 1) : d110967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7682, d110967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16921 q ha hb
    | true =>
      simp only [d7682, d110967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7683 q = 1) (hb : d107483 q = 1) : d110968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7683, d110968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7683, d110968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1006 q = 1) (hb : d107483 q = 1) : d11290 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d11290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16895 q ha hb
    | true =>
      simp only [d1006, d11290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1007 q = 1) (hb : d107483 q = 1) : d11291 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d11291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d11291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7688 q = 1) (hb : d107483 q = 1) : d110973 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7688, d110973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7688, d110973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7689 q = 1) (hb : d107483 q = 1) : d110974 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7689, d110974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7689, d110974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7690 q = 1) (hb : d107483 q = 1) : d110975 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7690, d110975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7690, d110975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7691 q = 1) (hb : d107483 q = 1) : d110976 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7691, d110976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7691, d110976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro16924 (p : Pattern) (ha : d7706 p = 1) (hb : d107483 p = 1) : d110982 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7682 q = 1) (hb : d107483 q = 1) : d110967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7682, d110967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16921 q ha hb
    | true =>
      simp only [d7682, d110967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7683 q = 1) (hb : d107483 q = 1) : d110968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7683, d110968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7683, d110968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7703 q = 1) (hb : d107483 q = 1) : d110979 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7703, d110979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7703, d110979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7704 q = 1) (hb : d107483 q = 1) : d110980 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7704, d110980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7704, d110980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7705 q = 1) (hb : d107483 q = 1) : d110981 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7705, d110981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7705, d110981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7706 q = 1) (hb : d107483 q = 1) : d110982 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7706, d110982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7706, d110982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16925 (p : Pattern) (ha : d85533 p = 1) (hb : d107483 p = 1) : d110988 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7692 q = 1) (hb : d107483 q = 1) : d110977 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7692, d110977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16922 q ha hb
    | true =>
      simp only [d7692, d110977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16923 q ha hb
  have h2 (q : Pattern) (ha : d85529 q = 1) (hb : d107483 q = 1) : d110978 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85529, d110978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85529, d110978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7707 q = 1) (hb : d107483 q = 1) : d110983 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7707, d110983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16924 q ha hb
    | true =>
      simp only [d7707, d110983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7708 q = 1) (hb : d107483 q = 1) : d110984 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7708, d110984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7708, d110984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85530 q = 1) (hb : d107483 q = 1) : d110985 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85530, d110985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85530, d110985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85531 q = 1) (hb : d107483 q = 1) : d110986 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85531, d110986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85531, d110986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85532 q = 1) (hb : d107483 q = 1) : d110987 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85532, d110987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85532, d110987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85533 q = 1) (hb : d107483 q = 1) : d110988 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85533, d110988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85533, d110988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16926 (p : Pattern) (ha : d85539 p = 1) (hb : d107483 p = 1) : d110994 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7588 q = 1) (hb : d107483 q = 1) : d110884 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7588, d110884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7588, d110884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16900 q ha hb
  have h2 (q : Pattern) (ha : d7589 q = 1) (hb : d107483 q = 1) : d110885 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7589, d110885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7589, d110885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7597 q = 1) (hb : d107483 q = 1) : d110893 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7597, d110893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16900 q ha hb
    | true =>
      simp only [d7597, d110893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16902 q ha hb
  have h4 (q : Pattern) (ha : d7598 q = 1) (hb : d107483 q = 1) : d110894 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7598, d110894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7598, d110894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7599 q = 1) (hb : d107483 q = 1) : d110895 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7599, d110895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7599, d110895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85517 q = 1) (hb : d107483 q = 1) : d110947 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85517, d110947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16911 q ha hb
    | true =>
      simp only [d85517, d110947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16918 q ha hb
  have h7 (q : Pattern) (ha : d7664 q = 1) (hb : d107483 q = 1) : d110949 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7664, d110949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16903 q ha hb
    | true =>
      simp only [d7664, d110949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16893 q ha hb
  have h8 (q : Pattern) (ha : d85518 q = 1) (hb : d107483 q = 1) : d110950 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85518, d110950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85518, d110950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85519 q = 1) (hb : d107483 q = 1) : d110951 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85519, d110951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85519, d110951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d85520 q = 1) (hb : d107483 q = 1) : d110952 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85520, d110952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85520, d110952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d85524 q = 1) (hb : d107483 q = 1) : d110956 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85524, d110956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85524, d110956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16919 q ha hb
  have h12 (q : Pattern) (ha : d960 q = 1) (hb : d107483 q = 1) : d11259 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, d11259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d960, d11259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16894 q ha hb
  have h13 (q : Pattern) (ha : d85525 q = 1) (hb : d107483 q = 1) : d110957 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85525, d110957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85525, d110957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85526 q = 1) (hb : d107483 q = 1) : d110958 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85526, d110958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85526, d110958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d85527 q = 1) (hb : d107483 q = 1) : d110959 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85527, d110959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85527, d110959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d85528 q = 1) (hb : d107483 q = 1) : d110960 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85528, d110960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85528, d110960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85534 q = 1) (hb : d107483 q = 1) : d110989 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85534, d110989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85534, d110989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16925 q ha hb
  have h18 (q : Pattern) (ha : d1070 q = 1) (hb : d107483 q = 1) : d11352 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, d11352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1070, d11352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16897 q ha hb
  have h19 (q : Pattern) (ha : d85535 q = 1) (hb : d107483 q = 1) : d110990 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85535, d110990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85535, d110990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d85536 q = 1) (hb : d107483 q = 1) : d110991 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85536, d110991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d85536, d110991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d85537 q = 1) (hb : d107483 q = 1) : d110992 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85537, d110992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d85537, d110992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d85538 q = 1) (hb : d107483 q = 1) : d110993 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85538, d110993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85538, d110993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d85539 q = 1) (hb : d107483 q = 1) : d110994 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85539, d110994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85539, d110994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro16927 (p : Pattern) (ha : d85545 p = 1) (hb : d107483 p = 1) : d111000 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85540 q = 1) (hb : d107483 q = 1) : d110995 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85540, d110995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85540, d110995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16926 q ha hb
  have h2 (q : Pattern) (ha : d85541 q = 1) (hb : d107483 q = 1) : d110996 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85541, d110996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85541, d110996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85542 q = 1) (hb : d107483 q = 1) : d110997 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85542, d110997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85542, d110997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85543 q = 1) (hb : d107483 q = 1) : d110998 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85543, d110998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85543, d110998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85544 q = 1) (hb : d107483 q = 1) : d110999 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85544, d110999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85544, d110999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85545 q = 1) (hb : d107483 q = 1) : d111000 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85545, d111000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85545, d111000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16928 (p : Pattern) (ha : d1152 p = 1) (hb : d107483 p = 1) : d11379 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1128 q = 1) : d1128 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1141 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1142 q = 1) (hb : d85721 q = 1) : d11369 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1142, d85721, d11369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1142, d85721, d11369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1143 q = 1) (hb : d85721 q = 1) : d11370 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1143, d11370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1143, d11370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1144 q = 1) (hb : d85721 q = 1) : d11371 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1144, d11371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1144, d11371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1146 q = 1) (hb : d85721 q = 1) : d11373 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1146, d11373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1146, d11373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1151 q = 1) (hb : d107483 q = 1) : d11378 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1151, d107483, d11378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1151, d107483, d11378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1152 q = 1) (hb : d107483 q = 1) : d11379 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1152, d11379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1152, d11379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro16929 (p : Pattern) (ha : d1162 p = 1) (hb : d107483 p = 1) : d11389 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d107483 q = 1) : d11380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16928 q ha hb
    | true =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d107483 q = 1) : d11381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d107483 q = 1) : d11386 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d11386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d11386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d107483 q = 1) : d11387 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d11387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1160, d11387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1161 q = 1) (hb : d107483 q = 1) : d11388 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1161, d11388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1161, d11388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1162 q = 1) (hb : d107483 q = 1) : d11389 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1162, d11389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1162, d11389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16930 (p : Pattern) (ha : d1172 p = 1) (hb : d107483 p = 1) : d11399 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d107483 q = 1) : d11380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16928 q ha hb
    | true =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d107483 q = 1) : d11381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d107483 q = 1) : d11386 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d11386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d11386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d107483 q = 1) : d11387 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d11387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1160, d11387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1161 q = 1) (hb : d107483 q = 1) : d11388 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1161, d11388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1161, d11388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1172 q = 1) (hb : d107483 q = 1) : d11399 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1172, d11399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1172, d11399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16931 (p : Pattern) (ha : d1361 p = 1) (hb : d107483 p = 1) : d11519 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1350 q = 1) (hb : d107483 q = 1) : d11508 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, d11508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16929 q ha hb
    | true =>
      simp only [d1350, d11508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1351 q = 1) (hb : d107483 q = 1) : d11509 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, d11509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1351, d11509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1352 q = 1) (hb : d107483 q = 1) : d11510 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, d11510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1352, d11510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1353 q = 1) (hb : d107483 q = 1) : d11511 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, d11511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, d11511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1354 q = 1) (hb : d107483 q = 1) : d11512 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, d11512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, d11512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1356 q = 1) (hb : d107483 q = 1) : d11514 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1356, d11514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16930 q ha hb
    | true =>
      simp only [d1356, d11514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1357 q = 1) (hb : d107483 q = 1) : d11515 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1357, d11515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1357, d11515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1358 q = 1) (hb : d107483 q = 1) : d11516 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1358, d11516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1358, d11516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1359 q = 1) (hb : d107483 q = 1) : d11517 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1359, d11517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1359, d11517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1360 q = 1) (hb : d107483 q = 1) : d11518 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1360, d11518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1360, d11518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1361 q = 1) (hb : d107483 q = 1) : d11519 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1361, d11519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1361, d11519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro16932 (p : Pattern) (ha : d1370 p = 1) (hb : d107483 p = 1) : d11528 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1356 q = 1) (hb : d107483 q = 1) : d11514 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1356, d11514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16930 q ha hb
    | true =>
      simp only [d1356, d11514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1357 q = 1) (hb : d107483 q = 1) : d11515 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1357, d11515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1357, d11515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1358 q = 1) (hb : d107483 q = 1) : d11516 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1358, d11516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1358, d11516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1359 q = 1) (hb : d107483 q = 1) : d11517 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1359, d11517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1359, d11517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1360 q = 1) (hb : d107483 q = 1) : d11518 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1360, d11518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1360, d11518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1370 q = 1) (hb : d107483 q = 1) : d11528 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1370, d11528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1370, d11528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16933 (p : Pattern) (ha : d1430 p = 1) (hb : d107483 p = 1) : d11559 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1401 q = 1) : d1401 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1411 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1412 q = 1) (hb : d85721 q = 1) : d11541 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, d85721, d11541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1412, d85721, d11541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1413 q = 1) (hb : d85721 q = 1) : d11542 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, d11542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1413, d11542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1414 q = 1) (hb : d85721 q = 1) : d11543 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, d11543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1414, d11543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1420 q = 1) (hb : d85721 q = 1) : d11549 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1420, d11549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1420, d11549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1429 q = 1) (hb : d107483 q = 1) : d11558 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1429, d107483, d11558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1429, d107483, d11558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1430 q = 1) (hb : d107483 q = 1) : d11559 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1430, d11559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1430, d11559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro16934 (p : Pattern) (ha : d1497 p = 1) (hb : d107483 p = 1) : d11615 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1431 q = 1) (hb : d107483 q = 1) : d11560 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1431, d11560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16933 q ha hb
    | true =>
      simp only [d1431, d11560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1432 q = 1) (hb : d107483 q = 1) : d11561 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, d11561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1432, d11561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1494 q = 1) (hb : d107483 q = 1) : d11612 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1494, d11612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1494, d11612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1495 q = 1) (hb : d107483 q = 1) : d11613 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1495, d11613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1495, d11613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1496 q = 1) (hb : d107483 q = 1) : d11614 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1496, d11614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1496, d11614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1497 q = 1) (hb : d107483 q = 1) : d11615 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1497, d11615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1497, d11615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16935 (p : Pattern) (ha : d1503 p = 1) (hb : d107483 p = 1) : d11621 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1498 q = 1) (hb : d107483 q = 1) : d11616 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1498, d11616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16934 q ha hb
    | true =>
      simp only [d1498, d11616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1499 q = 1) (hb : d107483 q = 1) : d11617 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1499, d11617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1499, d11617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1500 q = 1) (hb : d107483 q = 1) : d11618 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1500, d11618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1500, d11618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1501 q = 1) (hb : d107483 q = 1) : d11619 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1501, d11619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1501, d11619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1502 q = 1) (hb : d107483 q = 1) : d11620 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1502, d11620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1502, d11620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1503 q = 1) (hb : d107483 q = 1) : d11621 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1503, d11621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1503, d11621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16936 (p : Pattern) (ha : d7728 p = 1) (hb : d107483 p = 1) : d111004 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1126 q = 1) : d1126 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1128 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1129 q = 1) (hb : d85721 q = 1) : d11366 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1129, d85721, d11366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1129, d85721, d11366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1130 q = 1) (hb : d85721 q = 1) : d11367 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1130, d11367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1130, d11367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1131 q = 1) (hb : d85721 q = 1) : d11368 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1131, d11368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1131, d11368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d1128 q = 1) : d1128 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1141 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1142 q = 1) (hb : d85721 q = 1) : d11369 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1142, d85721, d11369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1142, d85721, d11369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1143 q = 1) (hb : d85721 q = 1) : d11370 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1143, d11370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1143, d11370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1144 q = 1) (hb : d85721 q = 1) : d11371 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1144, d11371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1144, d11371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1145 q = 1) (hb : d85721 q = 1) : d11372 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1145, d11372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1145, d11372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7727 q = 1) (hb : d107483 q = 1) : d111003 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7727, d107483, d111003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7727, d107483, d111003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d7728 q = 1) (hb : d107483 q = 1) : d111004 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7728, d111004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d7728, d111004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro16937 (p : Pattern) (ha : d7734 p = 1) (hb : d107483 p = 1) : d111010 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7729 q = 1) (hb : d107483 q = 1) : d111005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16936 q ha hb
    | true =>
      simp only [d7729, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7730 q = 1) (hb : d107483 q = 1) : d111006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d107483 q = 1) : d11380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16928 q ha hb
    | true =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d107483 q = 1) : d11381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7731 q = 1) (hb : d107483 q = 1) : d111007 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7731, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7732 q = 1) (hb : d107483 q = 1) : d111008 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7732, d111008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7732, d111008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7733 q = 1) (hb : d107483 q = 1) : d111009 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7733, d111009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7733, d111009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7734 q = 1) (hb : d107483 q = 1) : d111010 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7734, d111010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7734, d111010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16938 (p : Pattern) (ha : d7740 p = 1) (hb : d107483 p = 1) : d111016 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7735 q = 1) (hb : d107483 q = 1) : d111011 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7735, d111011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16937 q ha hb
    | true =>
      simp only [d7735, d111011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16929 q ha hb
  have h2 (q : Pattern) (ha : d7736 q = 1) (hb : d107483 q = 1) : d111012 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7736, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7736, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7737 q = 1) (hb : d107483 q = 1) : d111013 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7737, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7737, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7738 q = 1) (hb : d107483 q = 1) : d111014 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7738, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7738, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7739 q = 1) (hb : d107483 q = 1) : d111015 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7739, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7739, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7740 q = 1) (hb : d107483 q = 1) : d111016 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7740, d111016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7740, d111016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16939 (p : Pattern) (ha : d7743 p = 1) (hb : d107483 p = 1) : d111019 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7729 q = 1) (hb : d107483 q = 1) : d111005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16936 q ha hb
    | true =>
      simp only [d7729, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7730 q = 1) (hb : d107483 q = 1) : d111006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d107483 q = 1) : d11380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16928 q ha hb
    | true =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d107483 q = 1) : d11381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7731 q = 1) (hb : d107483 q = 1) : d111007 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7731, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7732 q = 1) (hb : d107483 q = 1) : d111008 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7732, d111008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7732, d111008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7733 q = 1) (hb : d107483 q = 1) : d111009 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7733, d111009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7733, d111009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7743 q = 1) (hb : d107483 q = 1) : d111019 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7743, d111019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7743, d111019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro16940 (p : Pattern) (ha : d7749 p = 1) (hb : d107483 p = 1) : d111025 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7735 q = 1) (hb : d107483 q = 1) : d111011 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7735, d111011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16937 q ha hb
    | true =>
      simp only [d7735, d111011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16929 q ha hb
  have h2 (q : Pattern) (ha : d7736 q = 1) (hb : d107483 q = 1) : d111012 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7736, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7736, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7737 q = 1) (hb : d107483 q = 1) : d111013 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7737, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7737, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7738 q = 1) (hb : d107483 q = 1) : d111014 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7738, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7738, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7739 q = 1) (hb : d107483 q = 1) : d111015 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7739, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7739, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7744 q = 1) (hb : d107483 q = 1) : d111020 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7744, d111020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16939 q ha hb
    | true =>
      simp only [d7744, d111020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16930 q ha hb
  have h7 (q : Pattern) (ha : d7745 q = 1) (hb : d107483 q = 1) : d111021 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7745, d111021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7745, d111021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7746 q = 1) (hb : d107483 q = 1) : d111022 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7746, d111022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7746, d111022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d7747 q = 1) (hb : d107483 q = 1) : d111023 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7747, d111023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7747, d111023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7748 q = 1) (hb : d107483 q = 1) : d111024 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7748, d111024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7748, d111024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7749 q = 1) (hb : d107483 q = 1) : d111025 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7749, d111025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7749, d111025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro16941 (p : Pattern) (ha : d7816 p = 1) (hb : d107483 p = 1) : d111081 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7735 q = 1) (hb : d107483 q = 1) : d111011 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7735, d111011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16937 q ha hb
    | true =>
      simp only [d7735, d111011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16929 q ha hb
  have h2 (q : Pattern) (ha : d7736 q = 1) (hb : d107483 q = 1) : d111012 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7736, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7736, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7737 q = 1) (hb : d107483 q = 1) : d111013 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7737, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7737, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7738 q = 1) (hb : d107483 q = 1) : d111014 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7738, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7738, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7739 q = 1) (hb : d107483 q = 1) : d111015 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7739, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7739, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1350 q = 1) (hb : d107483 q = 1) : d11508 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, d11508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16929 q ha hb
    | true =>
      simp only [d1350, d11508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1351 q = 1) (hb : d107483 q = 1) : d11509 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, d11509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1351, d11509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1352 q = 1) (hb : d107483 q = 1) : d11510 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, d11510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1352, d11510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1353 q = 1) (hb : d107483 q = 1) : d11511 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, d11511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, d11511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1354 q = 1) (hb : d107483 q = 1) : d11512 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, d11512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, d11512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7816 q = 1) (hb : d107483 q = 1) : d111081 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7816, d111081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7816, d111081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro16942 (p : Pattern) (ha : d1185 p = 1) (hb : d107483 p = 1) : d11412 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d107483 q = 1) : d11380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16928 q ha hb
    | true =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d107483 q = 1) : d11381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d107483 q = 1) : d11386 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d11386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d11386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d107483 q = 1) : d11387 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d11387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1160, d11387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1184 q = 1) (hb : d107483 q = 1) : d11411 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1184, d11411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1184, d11411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1185 q = 1) (hb : d107483 q = 1) : d11412 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1185, d11412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1185, d11412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16943 (p : Pattern) (ha : d1195 p = 1) (hb : d107483 p = 1) : d11422 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d107483 q = 1) : d11380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16928 q ha hb
    | true =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d107483 q = 1) : d11381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d107483 q = 1) : d11386 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d11386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d11386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1193 q = 1) (hb : d107483 q = 1) : d11420 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1193, d11420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1193, d11420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1194 q = 1) (hb : d107483 q = 1) : d11421 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1194, d11421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1194, d11421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1195 q = 1) (hb : d107483 q = 1) : d11422 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1195, d11422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1195, d11422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16944 (p : Pattern) (ha : d7754 p = 1) (hb : d107483 p = 1) : d111030 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7729 q = 1) (hb : d107483 q = 1) : d111005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16936 q ha hb
    | true =>
      simp only [d7729, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7730 q = 1) (hb : d107483 q = 1) : d111006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d107483 q = 1) : d11380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16928 q ha hb
    | true =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d107483 q = 1) : d11381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7731 q = 1) (hb : d107483 q = 1) : d111007 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7731, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7732 q = 1) (hb : d107483 q = 1) : d111008 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7732, d111008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7732, d111008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7753 q = 1) (hb : d107483 q = 1) : d111029 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7753, d111029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7753, d111029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7754 q = 1) (hb : d107483 q = 1) : d111030 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7754, d111030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7754, d111030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16945 (p : Pattern) (ha : d7761 p = 1) (hb : d107483 p = 1) : d111037 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7729 q = 1) (hb : d107483 q = 1) : d111005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16936 q ha hb
    | true =>
      simp only [d7729, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7730 q = 1) (hb : d107483 q = 1) : d111006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d107483 q = 1) : d11380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16928 q ha hb
    | true =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d107483 q = 1) : d11381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7731 q = 1) (hb : d107483 q = 1) : d111007 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7731, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7759 q = 1) (hb : d107483 q = 1) : d111035 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7759, d111035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7759, d111035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7760 q = 1) (hb : d107483 q = 1) : d111036 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7760, d111036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7760, d111036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7761 q = 1) (hb : d107483 q = 1) : d111037 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7761, d111037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7761, d111037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16946 (p : Pattern) (ha : d7766 p = 1) (hb : d107483 p = 1) : d111042 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1215 q = 1) : d1215 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1126 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1216 q = 1) (hb : d85721 q = 1) : d11426 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1216, d85721, d11426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1216, d85721, d11426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1217 q = 1) (hb : d85721 q = 1) : d11427 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1217, d11427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1217, d11427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1218 q = 1) (hb : d85721 q = 1) : d11428 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1218, d11428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1218, d11428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d1126 q = 1) : d1126 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1128 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1129 q = 1) (hb : d85721 q = 1) : d11366 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1129, d85721, d11366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1129, d85721, d11366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1130 q = 1) (hb : d85721 q = 1) : d11367 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1130, d11367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1130, d11367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1131 q = 1) (hb : d85721 q = 1) : d11368 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1131, d11368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1131, d11368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1219 q = 1) (hb : d85721 q = 1) : d11429 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1219, d11429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1219, d11429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7765 q = 1) (hb : d107483 q = 1) : d111041 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7765, d107483, d111041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7765, d107483, d111041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d7766 q = 1) (hb : d107483 q = 1) : d111042 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7766, d111042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d7766, d111042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro16947 (p : Pattern) (ha : d7772 p = 1) (hb : d107483 p = 1) : d111048 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7767 q = 1) (hb : d107483 q = 1) : d111043 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7767, d111043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16946 q ha hb
    | true =>
      simp only [d7767, d111043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7768 q = 1) (hb : d107483 q = 1) : d111044 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7768, d111044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7768, d111044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7729 q = 1) (hb : d107483 q = 1) : d111005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16936 q ha hb
    | true =>
      simp only [d7729, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7730 q = 1) (hb : d107483 q = 1) : d111006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7769 q = 1) (hb : d107483 q = 1) : d111045 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7769, d111045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7769, d111045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7770 q = 1) (hb : d107483 q = 1) : d111046 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7770, d111046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7770, d111046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7771 q = 1) (hb : d107483 q = 1) : d111047 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7771, d111047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7771, d111047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7772 q = 1) (hb : d107483 q = 1) : d111048 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7772, d111048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7772, d111048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16948 (p : Pattern) (ha : d7787 p = 1) (hb : d107483 p = 1) : d111054 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7729 q = 1) (hb : d107483 q = 1) : d111005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16936 q ha hb
    | true =>
      simp only [d7729, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7730 q = 1) (hb : d107483 q = 1) : d111006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7784 q = 1) (hb : d107483 q = 1) : d111051 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7784, d111051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7784, d111051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7785 q = 1) (hb : d107483 q = 1) : d111052 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7785, d111052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7785, d111052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7786 q = 1) (hb : d107483 q = 1) : d111053 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7786, d111053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7786, d111053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7787 q = 1) (hb : d107483 q = 1) : d111054 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7787, d111054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7787, d111054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16949 (p : Pattern) (ha : d85552 p = 1) (hb : d107483 p = 1) : d111060 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7755 q = 1) (hb : d107483 q = 1) : d111031 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7755, d111031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16944 q ha hb
    | true =>
      simp only [d7755, d111031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16942 q ha hb
  have h2 (q : Pattern) (ha : d7756 q = 1) (hb : d107483 q = 1) : d111032 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7756, d111032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7756, d111032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7757 q = 1) (hb : d107483 q = 1) : d111033 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7757, d111033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7757, d111033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7758 q = 1) (hb : d107483 q = 1) : d111034 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7758, d111034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7758, d111034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7762 q = 1) (hb : d107483 q = 1) : d111038 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7762, d111038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16945 q ha hb
    | true =>
      simp only [d7762, d111038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16943 q ha hb
  have h6 (q : Pattern) (ha : d7763 q = 1) (hb : d107483 q = 1) : d111039 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7763, d111039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7763, d111039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7764 q = 1) (hb : d107483 q = 1) : d111040 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7764, d111040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7764, d111040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7773 q = 1) (hb : d107483 q = 1) : d111049 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7773, d111049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16947 q ha hb
    | true =>
      simp only [d7773, d111049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16937 q ha hb
  have h9 (q : Pattern) (ha : d85548 q = 1) (hb : d107483 q = 1) : d111050 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85548, d111050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85548, d111050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7788 q = 1) (hb : d107483 q = 1) : d111055 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7788, d111055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16948 q ha hb
    | true =>
      simp only [d7788, d111055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d7789 q = 1) (hb : d107483 q = 1) : d111056 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7789, d111056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7789, d111056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d85549 q = 1) (hb : d107483 q = 1) : d111057 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85549, d111057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85549, d111057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85550 q = 1) (hb : d107483 q = 1) : d111058 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85550, d111058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85550, d111058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85551 q = 1) (hb : d107483 q = 1) : d111059 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85551, d111059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85551, d111059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85552 q = 1) (hb : d107483 q = 1) : d111060 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85552, d111060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85552, d111060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro16950 (p : Pattern) (ha : d1327 p = 1) (hb : d107483 p = 1) : d11484 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d107483 q = 1) : d11380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16928 q ha hb
    | true =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d107483 q = 1) : d11381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d107483 q = 1) : d11386 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d11386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d11386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d107483 q = 1) : d11387 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d11387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1160, d11387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1184 q = 1) (hb : d107483 q = 1) : d11411 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1184, d11411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1184, d11411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1327 q = 1) (hb : d107483 q = 1) : d11484 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1327, d11484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1327, d11484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16951 (p : Pattern) (ha : d1333 p = 1) (hb : d107483 p = 1) : d11490 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d107483 q = 1) : d11380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16928 q ha hb
    | true =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d107483 q = 1) : d11381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d107483 q = 1) : d11386 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d11386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d11386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1193 q = 1) (hb : d107483 q = 1) : d11420 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1193, d11420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1193, d11420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1194 q = 1) (hb : d107483 q = 1) : d11421 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1194, d11421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1194, d11421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1333 q = 1) (hb : d107483 q = 1) : d11490 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1333, d11490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1333, d11490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16952 (p : Pattern) (ha : d7794 p = 1) (hb : d107483 p = 1) : d111061 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7729 q = 1) (hb : d107483 q = 1) : d111005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16936 q ha hb
    | true =>
      simp only [d7729, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7730 q = 1) (hb : d107483 q = 1) : d111006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d107483 q = 1) : d11380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16928 q ha hb
    | true =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d107483 q = 1) : d11381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7731 q = 1) (hb : d107483 q = 1) : d111007 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7731, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7732 q = 1) (hb : d107483 q = 1) : d111008 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7732, d111008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7732, d111008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7753 q = 1) (hb : d107483 q = 1) : d111029 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7753, d111029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7753, d111029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7794 q = 1) (hb : d107483 q = 1) : d111061 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7794, d111061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7794, d111061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro16953 (p : Pattern) (ha : d7799 p = 1) (hb : d107483 p = 1) : d111066 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7729 q = 1) (hb : d107483 q = 1) : d111005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16936 q ha hb
    | true =>
      simp only [d7729, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7730 q = 1) (hb : d107483 q = 1) : d111006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d107483 q = 1) : d11380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16928 q ha hb
    | true =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d107483 q = 1) : d11381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7731 q = 1) (hb : d107483 q = 1) : d111007 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7731, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7759 q = 1) (hb : d107483 q = 1) : d111035 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7759, d111035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7759, d111035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7760 q = 1) (hb : d107483 q = 1) : d111036 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7760, d111036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7760, d111036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7799 q = 1) (hb : d107483 q = 1) : d111066 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7799, d111066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7799, d111066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro16954 (p : Pattern) (ha : d7803 p = 1) (hb : d107483 p = 1) : d111070 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7767 q = 1) (hb : d107483 q = 1) : d111043 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7767, d111043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16946 q ha hb
    | true =>
      simp only [d7767, d111043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7768 q = 1) (hb : d107483 q = 1) : d111044 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7768, d111044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7768, d111044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7729 q = 1) (hb : d107483 q = 1) : d111005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16936 q ha hb
    | true =>
      simp only [d7729, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7730 q = 1) (hb : d107483 q = 1) : d111006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7769 q = 1) (hb : d107483 q = 1) : d111045 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7769, d111045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7769, d111045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7770 q = 1) (hb : d107483 q = 1) : d111046 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7770, d111046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7770, d111046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7771 q = 1) (hb : d107483 q = 1) : d111047 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7771, d111047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7771, d111047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7803 q = 1) (hb : d107483 q = 1) : d111070 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7803, d111070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7803, d111070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro16955 (p : Pattern) (ha : d7808 p = 1) (hb : d107483 p = 1) : d111073 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7729 q = 1) (hb : d107483 q = 1) : d111005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16936 q ha hb
    | true =>
      simp only [d7729, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7730 q = 1) (hb : d107483 q = 1) : d111006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7784 q = 1) (hb : d107483 q = 1) : d111051 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7784, d111051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7784, d111051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7785 q = 1) (hb : d107483 q = 1) : d111052 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7785, d111052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7785, d111052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7786 q = 1) (hb : d107483 q = 1) : d111053 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7786, d111053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7786, d111053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7808 q = 1) (hb : d107483 q = 1) : d111073 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7808, d111073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7808, d111073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16956 (p : Pattern) (ha : d85557 p = 1) (hb : d107483 p = 1) : d111079 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7755 q = 1) (hb : d107483 q = 1) : d111031 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7755, d111031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16944 q ha hb
    | true =>
      simp only [d7755, d111031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16942 q ha hb
  have h2 (q : Pattern) (ha : d7756 q = 1) (hb : d107483 q = 1) : d111032 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7756, d111032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7756, d111032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7757 q = 1) (hb : d107483 q = 1) : d111033 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7757, d111033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7757, d111033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7758 q = 1) (hb : d107483 q = 1) : d111034 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7758, d111034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7758, d111034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7762 q = 1) (hb : d107483 q = 1) : d111038 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7762, d111038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16945 q ha hb
    | true =>
      simp only [d7762, d111038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16943 q ha hb
  have h6 (q : Pattern) (ha : d7763 q = 1) (hb : d107483 q = 1) : d111039 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7763, d111039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7763, d111039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7764 q = 1) (hb : d107483 q = 1) : d111040 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7764, d111040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7764, d111040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7773 q = 1) (hb : d107483 q = 1) : d111049 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7773, d111049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16947 q ha hb
    | true =>
      simp only [d7773, d111049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16937 q ha hb
  have h9 (q : Pattern) (ha : d85548 q = 1) (hb : d107483 q = 1) : d111050 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85548, d111050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85548, d111050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7788 q = 1) (hb : d107483 q = 1) : d111055 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7788, d111055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16948 q ha hb
    | true =>
      simp only [d7788, d111055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d7789 q = 1) (hb : d107483 q = 1) : d111056 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7789, d111056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7789, d111056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d85549 q = 1) (hb : d107483 q = 1) : d111057 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85549, d111057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85549, d111057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85550 q = 1) (hb : d107483 q = 1) : d111058 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85550, d111058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85550, d111058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85551 q = 1) (hb : d107483 q = 1) : d111059 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85551, d111059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85551, d111059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d7795 q = 1) (hb : d107483 q = 1) : d111062 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7795, d111062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16952 q ha hb
    | true =>
      simp only [d7795, d111062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16950 q ha hb
  have h16 (q : Pattern) (ha : d7796 q = 1) (hb : d107483 q = 1) : d111063 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7796, d111063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7796, d111063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d7797 q = 1) (hb : d107483 q = 1) : d111064 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7797, d111064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d7797, d111064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d7798 q = 1) (hb : d107483 q = 1) : d111065 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7798, d111065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7798, d111065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d7800 q = 1) (hb : d107483 q = 1) : d111067 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7800, d111067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16953 q ha hb
    | true =>
      simp only [d7800, d111067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16951 q ha hb
  have h20 (q : Pattern) (ha : d7801 q = 1) (hb : d107483 q = 1) : d111068 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7801, d111068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7801, d111068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d7802 q = 1) (hb : d107483 q = 1) : d111069 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7802, d111069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d7802, d111069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d7804 q = 1) (hb : d107483 q = 1) : d111071 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7804, d111071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16954 q ha hb
    | true =>
      simp only [d7804, d111071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16939 q ha hb
  have h23 (q : Pattern) (ha : d85553 q = 1) (hb : d107483 q = 1) : d111072 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85553, d111072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d85553, d111072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d7809 q = 1) (hb : d107483 q = 1) : d111074 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7809, d111074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16955 q ha hb
    | true =>
      simp only [d7809, d111074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d7810 q = 1) (hb : d107483 q = 1) : d111075 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7810, d111075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d7810, d111075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d85554 q = 1) (hb : d107483 q = 1) : d111076 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85554, d111076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d85554, d111076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d85555 q = 1) (hb : d107483 q = 1) : d111077 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85555, d111077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85555, d111077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d85556 q = 1) (hb : d107483 q = 1) : d111078 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85556, d111078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d85556, d111078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d85557 q = 1) (hb : d107483 q = 1) : d111079 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85557, d111079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85557, d111079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro16957 (p : Pattern) (ha : d85564 p = 1) (hb : d107483 p = 1) : d111088 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7804 q = 1) (hb : d107483 q = 1) : d111071 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7804, d111071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16954 q ha hb
    | true =>
      simp only [d7804, d111071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16939 q ha hb
  have h2 (q : Pattern) (ha : d85553 q = 1) (hb : d107483 q = 1) : d111072 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85553, d111072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85553, d111072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7809 q = 1) (hb : d107483 q = 1) : d111074 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7809, d111074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16955 q ha hb
    | true =>
      simp only [d7809, d111074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7810 q = 1) (hb : d107483 q = 1) : d111075 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7810, d111075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7810, d111075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85554 q = 1) (hb : d107483 q = 1) : d111076 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85554, d111076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85554, d111076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85562 q = 1) (hb : d107483 q = 1) : d111086 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85562, d111086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85562, d111086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85563 q = 1) (hb : d107483 q = 1) : d111087 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85563, d111087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85563, d111087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85564 q = 1) (hb : d107483 q = 1) : d111088 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85564, d111088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85564, d111088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16958 (p : Pattern) (ha : d7830 p = 1) (hb : d107483 p = 1) : d111095 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1390 q = 1) : d1390 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1396 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1397 q = 1) (hb : d85721 q = 1) : d11534 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1397, d85721, d11534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1397, d85721, d11534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1398 q = 1) (hb : d85721 q = 1) : d11535 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1398, d11535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1398, d11535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1399 q = 1) (hb : d85721 q = 1) : d11536 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1399, d11536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1399, d11536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d1396 q = 1) : d1396 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1401 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1402 q = 1) (hb : d85721 q = 1) : d11537 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, d85721, d11537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1402, d85721, d11537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1403 q = 1) (hb : d85721 q = 1) : d11538 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, d11538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1403, d11538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1404 q = 1) (hb : d85721 q = 1) : d11539 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, d11539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1404, d11539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1405 q = 1) (hb : d85721 q = 1) : d11540 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1405, d11540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1405, d11540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7829 q = 1) (hb : d107483 q = 1) : d111094 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7829, d107483, d111094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7829, d107483, d111094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d7830 q = 1) (hb : d107483 q = 1) : d111095 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7830, d111095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d7830, d111095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro16959 (p : Pattern) (ha : d7834 p = 1) (hb : d107483 p = 1) : d111099 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1396 q = 1) : d1396 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1401 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1402 q = 1) (hb : d85721 q = 1) : d11537 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, d85721, d11537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1402, d85721, d11537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1403 q = 1) (hb : d85721 q = 1) : d11538 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, d11538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1403, d11538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1404 q = 1) (hb : d85721 q = 1) : d11539 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, d11539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1404, d11539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d1401 q = 1) : d1401 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1411 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1412 q = 1) (hb : d85721 q = 1) : d11541 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, d85721, d11541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1412, d85721, d11541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1413 q = 1) (hb : d85721 q = 1) : d11542 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, d11542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1413, d11542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1414 q = 1) (hb : d85721 q = 1) : d11543 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, d11543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1414, d11543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1415 q = 1) (hb : d85721 q = 1) : d11544 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1415, d11544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1415, d11544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7833 q = 1) (hb : d107483 q = 1) : d111098 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7833, d107483, d111098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7833, d107483, d111098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d7834 q = 1) (hb : d107483 q = 1) : d111099 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7834, d111099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d7834, d111099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro16960 (p : Pattern) (ha : d7840 p = 1) (hb : d107483 p = 1) : d111105 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7831 q = 1) (hb : d107483 q = 1) : d111096 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7831, d111096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16958 q ha hb
    | true =>
      simp only [d7831, d111096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7832 q = 1) (hb : d107483 q = 1) : d111097 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7832, d111097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7832, d111097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7835 q = 1) (hb : d107483 q = 1) : d111100 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7835, d111100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16959 q ha hb
    | true =>
      simp only [d7835, d111100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7836 q = 1) (hb : d107483 q = 1) : d111101 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7836, d111101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7836, d111101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7837 q = 1) (hb : d107483 q = 1) : d111102 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7837, d111102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7837, d111102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7838 q = 1) (hb : d107483 q = 1) : d111103 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7838, d111103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7838, d111103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7839 q = 1) (hb : d107483 q = 1) : d111104 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7839, d111104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7839, d111104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7840 q = 1) (hb : d107483 q = 1) : d111105 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7840, d111105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7840, d111105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro16961 (p : Pattern) (ha : d7844 p = 1) (hb : d107483 p = 1) : d111109 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7835 q = 1) (hb : d107483 q = 1) : d111100 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7835, d111100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16959 q ha hb
    | true =>
      simp only [d7835, d111100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7836 q = 1) (hb : d107483 q = 1) : d111101 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7836, d111101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7836, d111101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1431 q = 1) (hb : d107483 q = 1) : d11560 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1431, d11560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16933 q ha hb
    | true =>
      simp only [d1431, d11560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1432 q = 1) (hb : d107483 q = 1) : d11561 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, d11561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1432, d11561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7841 q = 1) (hb : d107483 q = 1) : d111106 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7841, d111106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7841, d111106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7842 q = 1) (hb : d107483 q = 1) : d111107 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7842, d111107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7842, d111107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7843 q = 1) (hb : d107483 q = 1) : d111108 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7843, d111108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7843, d111108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7844 q = 1) (hb : d107483 q = 1) : d111109 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7844, d111109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7844, d111109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro16962 (p : Pattern) (ha : d7859 p = 1) (hb : d107483 p = 1) : d111115 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7835 q = 1) (hb : d107483 q = 1) : d111100 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7835, d111100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16959 q ha hb
    | true =>
      simp only [d7835, d111100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7836 q = 1) (hb : d107483 q = 1) : d111101 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7836, d111101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7836, d111101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7856 q = 1) (hb : d107483 q = 1) : d111112 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7856, d111112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7856, d111112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7857 q = 1) (hb : d107483 q = 1) : d111113 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7857, d111113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7857, d111113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7858 q = 1) (hb : d107483 q = 1) : d111114 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7858, d111114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7858, d111114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7859 q = 1) (hb : d107483 q = 1) : d111115 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7859, d111115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7859, d111115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16963 (p : Pattern) (ha : d85574 p = 1) (hb : d107483 p = 1) : d111121 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7845 q = 1) (hb : d107483 q = 1) : d111110 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7845, d111110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16960 q ha hb
    | true =>
      simp only [d7845, d111110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16961 q ha hb
  have h2 (q : Pattern) (ha : d85570 q = 1) (hb : d107483 q = 1) : d111111 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85570, d111111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85570, d111111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7860 q = 1) (hb : d107483 q = 1) : d111116 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7860, d111116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16962 q ha hb
    | true =>
      simp only [d7860, d111116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7861 q = 1) (hb : d107483 q = 1) : d111117 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7861, d111117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7861, d111117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85571 q = 1) (hb : d107483 q = 1) : d111118 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85571, d111118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85571, d111118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85572 q = 1) (hb : d107483 q = 1) : d111119 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85572, d111119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85572, d111119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85573 q = 1) (hb : d107483 q = 1) : d111120 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85573, d111120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85573, d111120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85574 q = 1) (hb : d107483 q = 1) : d111121 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85574, d111121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85574, d111121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16964 (p : Pattern) (ha : d85580 p = 1) (hb : d107483 p = 1) : d111127 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7741 q = 1) (hb : d107483 q = 1) : d111017 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7741, d111017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7741, d111017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16938 q ha hb
  have h2 (q : Pattern) (ha : d7742 q = 1) (hb : d107483 q = 1) : d111018 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7742, d111018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7742, d111018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7750 q = 1) (hb : d107483 q = 1) : d111026 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7750, d111026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16938 q ha hb
    | true =>
      simp only [d7750, d111026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16940 q ha hb
  have h4 (q : Pattern) (ha : d7751 q = 1) (hb : d107483 q = 1) : d111027 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7751, d111027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7751, d111027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7752 q = 1) (hb : d107483 q = 1) : d111028 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7752, d111028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7752, d111028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85558 q = 1) (hb : d107483 q = 1) : d111080 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85558, d111080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16949 q ha hb
    | true =>
      simp only [d85558, d111080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16956 q ha hb
  have h7 (q : Pattern) (ha : d7817 q = 1) (hb : d107483 q = 1) : d111082 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7817, d111082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16941 q ha hb
    | true =>
      simp only [d7817, d111082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16931 q ha hb
  have h8 (q : Pattern) (ha : d85559 q = 1) (hb : d107483 q = 1) : d111083 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85559, d111083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85559, d111083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85560 q = 1) (hb : d107483 q = 1) : d111084 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85560, d111084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85560, d111084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d85561 q = 1) (hb : d107483 q = 1) : d111085 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85561, d111085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85561, d111085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d85565 q = 1) (hb : d107483 q = 1) : d111089 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85565, d111089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85565, d111089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16957 q ha hb
  have h12 (q : Pattern) (ha : d1371 q = 1) (hb : d107483 q = 1) : d11529 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1371, d11529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1371, d11529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16932 q ha hb
  have h13 (q : Pattern) (ha : d85566 q = 1) (hb : d107483 q = 1) : d111090 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85566, d111090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85566, d111090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85567 q = 1) (hb : d107483 q = 1) : d111091 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85567, d111091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85567, d111091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d85568 q = 1) (hb : d107483 q = 1) : d111092 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85568, d111092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85568, d111092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d85569 q = 1) (hb : d107483 q = 1) : d111093 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85569, d111093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85569, d111093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85575 q = 1) (hb : d107483 q = 1) : d111122 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85575, d111122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85575, d111122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16963 q ha hb
  have h18 (q : Pattern) (ha : d1504 q = 1) (hb : d107483 q = 1) : d11622 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1504, d11622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1504, d11622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16935 q ha hb
  have h19 (q : Pattern) (ha : d85576 q = 1) (hb : d107483 q = 1) : d111123 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85576, d111123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85576, d111123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d85577 q = 1) (hb : d107483 q = 1) : d111124 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85577, d111124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d85577, d111124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d85578 q = 1) (hb : d107483 q = 1) : d111125 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85578, d111125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d85578, d111125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d85579 q = 1) (hb : d107483 q = 1) : d111126 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85579, d111126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85579, d111126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d85580 q = 1) (hb : d107483 q = 1) : d111127 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85580, d111127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85580, d111127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro16965 (p : Pattern) (ha : d85586 p = 1) (hb : d107483 p = 1) : d111133 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85581 q = 1) (hb : d107483 q = 1) : d111128 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85581, d111128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85581, d111128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16964 q ha hb
  have h2 (q : Pattern) (ha : d85582 q = 1) (hb : d107483 q = 1) : d111129 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85582, d111129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85582, d111129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85583 q = 1) (hb : d107483 q = 1) : d111130 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85583, d111130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85583, d111130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85584 q = 1) (hb : d107483 q = 1) : d111131 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85584, d111131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85584, d111131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85585 q = 1) (hb : d107483 q = 1) : d111132 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85585, d111132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85585, d111132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85586 q = 1) (hb : d107483 q = 1) : d111133 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85586, d111133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85586, d111133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16966 (p : Pattern) (ha : d1613 p = 1) (hb : d107483 p = 1) : d11650 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1589 q = 1) : d1589 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1602 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1603 q = 1) (hb : d85721 q = 1) : d11640 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1603, d85721, d11640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1603, d85721, d11640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1604 q = 1) (hb : d85721 q = 1) : d11641 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1604, d11641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1604, d11641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1605 q = 1) (hb : d85721 q = 1) : d11642 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1605, d11642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1605, d11642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1607 q = 1) (hb : d85721 q = 1) : d11644 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1607, d11644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1607, d11644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1612 q = 1) (hb : d107483 q = 1) : d11649 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1612, d107483, d11649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1612, d107483, d11649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1613 q = 1) (hb : d107483 q = 1) : d11650 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1613, d11650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1613, d11650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro16967 (p : Pattern) (ha : d1623 p = 1) (hb : d107483 p = 1) : d11660 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d107483 q = 1) : d11651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16966 q ha hb
    | true =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d107483 q = 1) : d11652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d107483 q = 1) : d11657 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d11657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d11657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d107483 q = 1) : d11658 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d11658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1621, d11658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1622 q = 1) (hb : d107483 q = 1) : d11659 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1622, d11659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1622, d11659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1623 q = 1) (hb : d107483 q = 1) : d11660 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1623, d11660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1623, d11660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16968 (p : Pattern) (ha : d1633 p = 1) (hb : d107483 p = 1) : d11670 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d107483 q = 1) : d11651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16966 q ha hb
    | true =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d107483 q = 1) : d11652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d107483 q = 1) : d11657 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d11657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d11657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d107483 q = 1) : d11658 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d11658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1621, d11658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1622 q = 1) (hb : d107483 q = 1) : d11659 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1622, d11659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1622, d11659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1633 q = 1) (hb : d107483 q = 1) : d11670 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1633, d11670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1633, d11670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16969 (p : Pattern) (ha : d1838 p = 1) (hb : d107483 p = 1) : d11790 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1827 q = 1) (hb : d107483 q = 1) : d11779 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, d11779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16967 q ha hb
    | true =>
      simp only [d1827, d11779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1828 q = 1) (hb : d107483 q = 1) : d11780 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, d11780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1828, d11780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1829 q = 1) (hb : d107483 q = 1) : d11781 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, d11781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1829, d11781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1830 q = 1) (hb : d107483 q = 1) : d11782 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, d11782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, d11782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1831 q = 1) (hb : d107483 q = 1) : d11783 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, d11783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, d11783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1833 q = 1) (hb : d107483 q = 1) : d11785 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1833, d11785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16968 q ha hb
    | true =>
      simp only [d1833, d11785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1834 q = 1) (hb : d107483 q = 1) : d11786 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1834, d11786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1834, d11786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1835 q = 1) (hb : d107483 q = 1) : d11787 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1835, d11787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1835, d11787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1836 q = 1) (hb : d107483 q = 1) : d11788 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1836, d11788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1836, d11788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1837 q = 1) (hb : d107483 q = 1) : d11789 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1837, d11789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1837, d11789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1838 q = 1) (hb : d107483 q = 1) : d11790 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1838, d11790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1838, d11790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro16970 (p : Pattern) (ha : d1847 p = 1) (hb : d107483 p = 1) : d11799 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1833 q = 1) (hb : d107483 q = 1) : d11785 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1833, d11785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16968 q ha hb
    | true =>
      simp only [d1833, d11785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1834 q = 1) (hb : d107483 q = 1) : d11786 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1834, d11786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1834, d11786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1835 q = 1) (hb : d107483 q = 1) : d11787 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1835, d11787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1835, d11787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1836 q = 1) (hb : d107483 q = 1) : d11788 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1836, d11788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1836, d11788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1837 q = 1) (hb : d107483 q = 1) : d11789 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1837, d11789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1837, d11789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1847 q = 1) (hb : d107483 q = 1) : d11799 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1847, d11799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1847, d11799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16971 (p : Pattern) (ha : d1907 p = 1) (hb : d107483 p = 1) : d11830 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1878 q = 1) : d1878 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1888 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1889 q = 1) (hb : d85721 q = 1) : d11812 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, d85721, d11812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1889, d85721, d11812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1890 q = 1) (hb : d85721 q = 1) : d11813 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, d11813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1890, d11813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1891 q = 1) (hb : d85721 q = 1) : d11814 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, d11814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1891, d11814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1897 q = 1) (hb : d85721 q = 1) : d11820 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1897, d11820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1897, d11820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1906 q = 1) (hb : d107483 q = 1) : d11829 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1906, d107483, d11829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1906, d107483, d11829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1907 q = 1) (hb : d107483 q = 1) : d11830 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1907, d11830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1907, d11830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro16972 (p : Pattern) (ha : d1974 p = 1) (hb : d107483 p = 1) : d11886 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1908 q = 1) (hb : d107483 q = 1) : d11831 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, d11831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16971 q ha hb
    | true =>
      simp only [d1908, d11831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1909 q = 1) (hb : d107483 q = 1) : d11832 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, d11832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1909, d11832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1971 q = 1) (hb : d107483 q = 1) : d11883 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1971, d11883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1971, d11883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1972 q = 1) (hb : d107483 q = 1) : d11884 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1972, d11884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1972, d11884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1973 q = 1) (hb : d107483 q = 1) : d11885 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1973, d11885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1973, d11885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1974 q = 1) (hb : d107483 q = 1) : d11886 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1974, d11886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1974, d11886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16973 (p : Pattern) (ha : d1980 p = 1) (hb : d107483 p = 1) : d11892 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1975 q = 1) (hb : d107483 q = 1) : d11887 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1975, d11887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16972 q ha hb
    | true =>
      simp only [d1975, d11887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1976 q = 1) (hb : d107483 q = 1) : d11888 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1976, d11888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1976, d11888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1977 q = 1) (hb : d107483 q = 1) : d11889 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1977, d11889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1977, d11889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1978 q = 1) (hb : d107483 q = 1) : d11890 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1978, d11890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1978, d11890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1979 q = 1) (hb : d107483 q = 1) : d11891 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1979, d11891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1979, d11891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1980 q = 1) (hb : d107483 q = 1) : d11892 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1980, d11892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1980, d11892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16974 (p : Pattern) (ha : d7882 p = 1) (hb : d107483 p = 1) : d111138 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1587 q = 1) : d1587 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1589 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1590 q = 1) (hb : d85721 q = 1) : d11637 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1590, d85721, d11637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1590, d85721, d11637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1591 q = 1) (hb : d85721 q = 1) : d11638 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1591, d11638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1591, d11638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1592 q = 1) (hb : d85721 q = 1) : d11639 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1592, d11639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1592, d11639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d1589 q = 1) : d1589 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1602 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1603 q = 1) (hb : d85721 q = 1) : d11640 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1603, d85721, d11640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1603, d85721, d11640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1604 q = 1) (hb : d85721 q = 1) : d11641 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1604, d11641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1604, d11641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1605 q = 1) (hb : d85721 q = 1) : d11642 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1605, d11642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1605, d11642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1606 q = 1) (hb : d85721 q = 1) : d11643 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1606, d11643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1606, d11643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7881 q = 1) (hb : d107483 q = 1) : d111137 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7881, d107483, d111137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7881, d107483, d111137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d7882 q = 1) (hb : d107483 q = 1) : d111138 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7882, d111138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d7882, d111138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro16975 (p : Pattern) (ha : d7888 p = 1) (hb : d107483 p = 1) : d111144 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7883 q = 1) (hb : d107483 q = 1) : d111139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16974 q ha hb
    | true =>
      simp only [d7883, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7884 q = 1) (hb : d107483 q = 1) : d111140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d107483 q = 1) : d11651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16966 q ha hb
    | true =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d107483 q = 1) : d11652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7885 q = 1) (hb : d107483 q = 1) : d111141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7885, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7886 q = 1) (hb : d107483 q = 1) : d111142 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7886, d111142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7886, d111142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7887 q = 1) (hb : d107483 q = 1) : d111143 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7887, d111143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7887, d111143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7888 q = 1) (hb : d107483 q = 1) : d111144 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7888, d111144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7888, d111144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16976 (p : Pattern) (ha : d7894 p = 1) (hb : d107483 p = 1) : d111150 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7889 q = 1) (hb : d107483 q = 1) : d111145 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7889, d111145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16975 q ha hb
    | true =>
      simp only [d7889, d111145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16967 q ha hb
  have h2 (q : Pattern) (ha : d7890 q = 1) (hb : d107483 q = 1) : d111146 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7890, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7890, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7891 q = 1) (hb : d107483 q = 1) : d111147 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7891, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7891, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7892 q = 1) (hb : d107483 q = 1) : d111148 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7892, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7892, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7893 q = 1) (hb : d107483 q = 1) : d111149 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7893, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7893, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7894 q = 1) (hb : d107483 q = 1) : d111150 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7894, d111150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7894, d111150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16977 (p : Pattern) (ha : d7897 p = 1) (hb : d107483 p = 1) : d111153 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7883 q = 1) (hb : d107483 q = 1) : d111139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16974 q ha hb
    | true =>
      simp only [d7883, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7884 q = 1) (hb : d107483 q = 1) : d111140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d107483 q = 1) : d11651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16966 q ha hb
    | true =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d107483 q = 1) : d11652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7885 q = 1) (hb : d107483 q = 1) : d111141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7885, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7886 q = 1) (hb : d107483 q = 1) : d111142 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7886, d111142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7886, d111142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7887 q = 1) (hb : d107483 q = 1) : d111143 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7887, d111143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7887, d111143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7897 q = 1) (hb : d107483 q = 1) : d111153 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7897, d111153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7897, d111153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro16978 (p : Pattern) (ha : d7903 p = 1) (hb : d107483 p = 1) : d111159 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7889 q = 1) (hb : d107483 q = 1) : d111145 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7889, d111145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16975 q ha hb
    | true =>
      simp only [d7889, d111145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16967 q ha hb
  have h2 (q : Pattern) (ha : d7890 q = 1) (hb : d107483 q = 1) : d111146 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7890, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7890, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7891 q = 1) (hb : d107483 q = 1) : d111147 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7891, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7891, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7892 q = 1) (hb : d107483 q = 1) : d111148 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7892, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7892, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7893 q = 1) (hb : d107483 q = 1) : d111149 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7893, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7893, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7898 q = 1) (hb : d107483 q = 1) : d111154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7898, d111154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16977 q ha hb
    | true =>
      simp only [d7898, d111154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16968 q ha hb
  have h7 (q : Pattern) (ha : d7899 q = 1) (hb : d107483 q = 1) : d111155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7899, d111155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7899, d111155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7900 q = 1) (hb : d107483 q = 1) : d111156 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7900, d111156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7900, d111156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d7901 q = 1) (hb : d107483 q = 1) : d111157 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7901, d111157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7901, d111157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7902 q = 1) (hb : d107483 q = 1) : d111158 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7902, d111158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7902, d111158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7903 q = 1) (hb : d107483 q = 1) : d111159 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7903, d111159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7903, d111159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro16979 (p : Pattern) (ha : d7970 p = 1) (hb : d107483 p = 1) : d111215 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7889 q = 1) (hb : d107483 q = 1) : d111145 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7889, d111145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16975 q ha hb
    | true =>
      simp only [d7889, d111145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16967 q ha hb
  have h2 (q : Pattern) (ha : d7890 q = 1) (hb : d107483 q = 1) : d111146 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7890, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7890, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7891 q = 1) (hb : d107483 q = 1) : d111147 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7891, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7891, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7892 q = 1) (hb : d107483 q = 1) : d111148 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7892, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7892, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7893 q = 1) (hb : d107483 q = 1) : d111149 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7893, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7893, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1827 q = 1) (hb : d107483 q = 1) : d11779 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, d11779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16967 q ha hb
    | true =>
      simp only [d1827, d11779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1828 q = 1) (hb : d107483 q = 1) : d11780 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, d11780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1828, d11780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1829 q = 1) (hb : d107483 q = 1) : d11781 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, d11781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1829, d11781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1830 q = 1) (hb : d107483 q = 1) : d11782 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, d11782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, d11782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1831 q = 1) (hb : d107483 q = 1) : d11783 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, d11783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, d11783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7970 q = 1) (hb : d107483 q = 1) : d111215 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7970, d111215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7970, d111215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro16980 (p : Pattern) (ha : d1646 p = 1) (hb : d107483 p = 1) : d11683 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d107483 q = 1) : d11651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16966 q ha hb
    | true =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d107483 q = 1) : d11652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d107483 q = 1) : d11657 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d11657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d11657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d107483 q = 1) : d11658 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d11658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1621, d11658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1645 q = 1) (hb : d107483 q = 1) : d11682 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1645, d11682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1645, d11682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1646 q = 1) (hb : d107483 q = 1) : d11683 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1646, d11683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1646, d11683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16981 (p : Pattern) (ha : d1656 p = 1) (hb : d107483 p = 1) : d11693 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d107483 q = 1) : d11651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16966 q ha hb
    | true =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d107483 q = 1) : d11652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d107483 q = 1) : d11657 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d11657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d11657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1654 q = 1) (hb : d107483 q = 1) : d11691 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1654, d11691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1654, d11691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1655 q = 1) (hb : d107483 q = 1) : d11692 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1655, d11692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1655, d11692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1656 q = 1) (hb : d107483 q = 1) : d11693 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1656, d11693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1656, d11693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16982 (p : Pattern) (ha : d7908 p = 1) (hb : d107483 p = 1) : d111164 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7883 q = 1) (hb : d107483 q = 1) : d111139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16974 q ha hb
    | true =>
      simp only [d7883, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7884 q = 1) (hb : d107483 q = 1) : d111140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d107483 q = 1) : d11651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16966 q ha hb
    | true =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d107483 q = 1) : d11652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7885 q = 1) (hb : d107483 q = 1) : d111141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7885, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7886 q = 1) (hb : d107483 q = 1) : d111142 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7886, d111142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7886, d111142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7907 q = 1) (hb : d107483 q = 1) : d111163 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7907, d111163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7907, d111163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7908 q = 1) (hb : d107483 q = 1) : d111164 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7908, d111164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7908, d111164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16983 (p : Pattern) (ha : d7915 p = 1) (hb : d107483 p = 1) : d111171 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7883 q = 1) (hb : d107483 q = 1) : d111139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16974 q ha hb
    | true =>
      simp only [d7883, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7884 q = 1) (hb : d107483 q = 1) : d111140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d107483 q = 1) : d11651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16966 q ha hb
    | true =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d107483 q = 1) : d11652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7885 q = 1) (hb : d107483 q = 1) : d111141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7885, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7913 q = 1) (hb : d107483 q = 1) : d111169 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7913, d111169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7913, d111169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7914 q = 1) (hb : d107483 q = 1) : d111170 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7914, d111170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7914, d111170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7915 q = 1) (hb : d107483 q = 1) : d111171 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7915, d111171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7915, d111171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16984 (p : Pattern) (ha : d7920 p = 1) (hb : d107483 p = 1) : d111176 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1670 q = 1) : d1670 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1587 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1671 q = 1) (hb : d85721 q = 1) : d11697 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1671, d85721, d11697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1671, d85721, d11697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1672 q = 1) (hb : d85721 q = 1) : d11698 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1672, d11698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1672, d11698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1673 q = 1) (hb : d85721 q = 1) : d11699 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1673, d11699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1673, d11699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d1587 q = 1) : d1587 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1589 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1590 q = 1) (hb : d85721 q = 1) : d11637 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1590, d85721, d11637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1590, d85721, d11637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1591 q = 1) (hb : d85721 q = 1) : d11638 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1591, d11638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1591, d11638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1592 q = 1) (hb : d85721 q = 1) : d11639 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1592, d11639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1592, d11639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1674 q = 1) (hb : d85721 q = 1) : d11700 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1674, d11700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1674, d11700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7919 q = 1) (hb : d107483 q = 1) : d111175 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7919, d107483, d111175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7919, d107483, d111175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d7920 q = 1) (hb : d107483 q = 1) : d111176 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7920, d111176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d7920, d111176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro16985 (p : Pattern) (ha : d7926 p = 1) (hb : d107483 p = 1) : d111182 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7921 q = 1) (hb : d107483 q = 1) : d111177 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7921, d111177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16984 q ha hb
    | true =>
      simp only [d7921, d111177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7922 q = 1) (hb : d107483 q = 1) : d111178 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7922, d111178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7922, d111178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7883 q = 1) (hb : d107483 q = 1) : d111139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16974 q ha hb
    | true =>
      simp only [d7883, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7884 q = 1) (hb : d107483 q = 1) : d111140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7923 q = 1) (hb : d107483 q = 1) : d111179 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7923, d111179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7923, d111179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7924 q = 1) (hb : d107483 q = 1) : d111180 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7924, d111180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7924, d111180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7925 q = 1) (hb : d107483 q = 1) : d111181 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7925, d111181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7925, d111181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7926 q = 1) (hb : d107483 q = 1) : d111182 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7926, d111182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7926, d111182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16986 (p : Pattern) (ha : d7941 p = 1) (hb : d107483 p = 1) : d111188 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7883 q = 1) (hb : d107483 q = 1) : d111139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16974 q ha hb
    | true =>
      simp only [d7883, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7884 q = 1) (hb : d107483 q = 1) : d111140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7938 q = 1) (hb : d107483 q = 1) : d111185 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7938, d111185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7938, d111185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7939 q = 1) (hb : d107483 q = 1) : d111186 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7939, d111186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7939, d111186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7940 q = 1) (hb : d107483 q = 1) : d111187 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7940, d111187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7940, d111187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7941 q = 1) (hb : d107483 q = 1) : d111188 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7941, d111188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7941, d111188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16987 (p : Pattern) (ha : d85594 p = 1) (hb : d107483 p = 1) : d111194 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7909 q = 1) (hb : d107483 q = 1) : d111165 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7909, d111165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16982 q ha hb
    | true =>
      simp only [d7909, d111165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16980 q ha hb
  have h2 (q : Pattern) (ha : d7910 q = 1) (hb : d107483 q = 1) : d111166 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7910, d111166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7910, d111166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7911 q = 1) (hb : d107483 q = 1) : d111167 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7911, d111167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7911, d111167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7912 q = 1) (hb : d107483 q = 1) : d111168 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7912, d111168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7912, d111168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7916 q = 1) (hb : d107483 q = 1) : d111172 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7916, d111172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16983 q ha hb
    | true =>
      simp only [d7916, d111172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16981 q ha hb
  have h6 (q : Pattern) (ha : d7917 q = 1) (hb : d107483 q = 1) : d111173 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7917, d111173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7917, d111173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7918 q = 1) (hb : d107483 q = 1) : d111174 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7918, d111174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7918, d111174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7927 q = 1) (hb : d107483 q = 1) : d111183 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7927, d111183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16985 q ha hb
    | true =>
      simp only [d7927, d111183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16975 q ha hb
  have h9 (q : Pattern) (ha : d85590 q = 1) (hb : d107483 q = 1) : d111184 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85590, d111184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85590, d111184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7942 q = 1) (hb : d107483 q = 1) : d111189 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7942, d111189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16986 q ha hb
    | true =>
      simp only [d7942, d111189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d7943 q = 1) (hb : d107483 q = 1) : d111190 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7943, d111190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7943, d111190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d85591 q = 1) (hb : d107483 q = 1) : d111191 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85591, d111191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85591, d111191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85592 q = 1) (hb : d107483 q = 1) : d111192 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85592, d111192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85592, d111192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85593 q = 1) (hb : d107483 q = 1) : d111193 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85593, d111193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85593, d111193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85594 q = 1) (hb : d107483 q = 1) : d111194 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85594, d111194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85594, d111194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro16988 (p : Pattern) (ha : d1804 p = 1) (hb : d107483 p = 1) : d11755 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d107483 q = 1) : d11651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16966 q ha hb
    | true =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d107483 q = 1) : d11652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d107483 q = 1) : d11657 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d11657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d11657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d107483 q = 1) : d11658 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d11658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1621, d11658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1645 q = 1) (hb : d107483 q = 1) : d11682 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1645, d11682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1645, d11682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1804 q = 1) (hb : d107483 q = 1) : d11755 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1804, d11755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1804, d11755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16989 (p : Pattern) (ha : d1810 p = 1) (hb : d107483 p = 1) : d11761 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d107483 q = 1) : d11651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16966 q ha hb
    | true =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d107483 q = 1) : d11652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d107483 q = 1) : d11657 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d11657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d11657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1654 q = 1) (hb : d107483 q = 1) : d11691 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1654, d11691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1654, d11691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1655 q = 1) (hb : d107483 q = 1) : d11692 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1655, d11692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1655, d11692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1810 q = 1) (hb : d107483 q = 1) : d11761 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1810, d11761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1810, d11761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16990 (p : Pattern) (ha : d7948 p = 1) (hb : d107483 p = 1) : d111195 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7883 q = 1) (hb : d107483 q = 1) : d111139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16974 q ha hb
    | true =>
      simp only [d7883, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7884 q = 1) (hb : d107483 q = 1) : d111140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d107483 q = 1) : d11651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16966 q ha hb
    | true =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d107483 q = 1) : d11652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7885 q = 1) (hb : d107483 q = 1) : d111141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7885, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7886 q = 1) (hb : d107483 q = 1) : d111142 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7886, d111142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7886, d111142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7907 q = 1) (hb : d107483 q = 1) : d111163 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7907, d111163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7907, d111163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7948 q = 1) (hb : d107483 q = 1) : d111195 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7948, d111195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7948, d111195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro16991 (p : Pattern) (ha : d7953 p = 1) (hb : d107483 p = 1) : d111200 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7883 q = 1) (hb : d107483 q = 1) : d111139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16974 q ha hb
    | true =>
      simp only [d7883, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7884 q = 1) (hb : d107483 q = 1) : d111140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d107483 q = 1) : d11651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16966 q ha hb
    | true =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d107483 q = 1) : d11652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7885 q = 1) (hb : d107483 q = 1) : d111141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7885, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7913 q = 1) (hb : d107483 q = 1) : d111169 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7913, d111169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7913, d111169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7914 q = 1) (hb : d107483 q = 1) : d111170 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7914, d111170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7914, d111170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7953 q = 1) (hb : d107483 q = 1) : d111200 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7953, d111200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7953, d111200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro16992 (p : Pattern) (ha : d7957 p = 1) (hb : d107483 p = 1) : d111204 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7921 q = 1) (hb : d107483 q = 1) : d111177 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7921, d111177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16984 q ha hb
    | true =>
      simp only [d7921, d111177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7922 q = 1) (hb : d107483 q = 1) : d111178 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7922, d111178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7922, d111178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7883 q = 1) (hb : d107483 q = 1) : d111139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16974 q ha hb
    | true =>
      simp only [d7883, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7884 q = 1) (hb : d107483 q = 1) : d111140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7923 q = 1) (hb : d107483 q = 1) : d111179 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7923, d111179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7923, d111179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7924 q = 1) (hb : d107483 q = 1) : d111180 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7924, d111180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7924, d111180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7925 q = 1) (hb : d107483 q = 1) : d111181 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7925, d111181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7925, d111181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7957 q = 1) (hb : d107483 q = 1) : d111204 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7957, d111204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7957, d111204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro16993 (p : Pattern) (ha : d7962 p = 1) (hb : d107483 p = 1) : d111207 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7883 q = 1) (hb : d107483 q = 1) : d111139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16974 q ha hb
    | true =>
      simp only [d7883, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7884 q = 1) (hb : d107483 q = 1) : d111140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7938 q = 1) (hb : d107483 q = 1) : d111185 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7938, d111185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7938, d111185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7939 q = 1) (hb : d107483 q = 1) : d111186 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7939, d111186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7939, d111186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7940 q = 1) (hb : d107483 q = 1) : d111187 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7940, d111187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7940, d111187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7962 q = 1) (hb : d107483 q = 1) : d111207 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7962, d111207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7962, d111207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16994 (p : Pattern) (ha : d85599 p = 1) (hb : d107483 p = 1) : d111213 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7909 q = 1) (hb : d107483 q = 1) : d111165 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7909, d111165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16982 q ha hb
    | true =>
      simp only [d7909, d111165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16980 q ha hb
  have h2 (q : Pattern) (ha : d7910 q = 1) (hb : d107483 q = 1) : d111166 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7910, d111166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7910, d111166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7911 q = 1) (hb : d107483 q = 1) : d111167 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7911, d111167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7911, d111167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7912 q = 1) (hb : d107483 q = 1) : d111168 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7912, d111168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7912, d111168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7916 q = 1) (hb : d107483 q = 1) : d111172 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7916, d111172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16983 q ha hb
    | true =>
      simp only [d7916, d111172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16981 q ha hb
  have h6 (q : Pattern) (ha : d7917 q = 1) (hb : d107483 q = 1) : d111173 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7917, d111173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7917, d111173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7918 q = 1) (hb : d107483 q = 1) : d111174 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7918, d111174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7918, d111174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7927 q = 1) (hb : d107483 q = 1) : d111183 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7927, d111183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16985 q ha hb
    | true =>
      simp only [d7927, d111183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16975 q ha hb
  have h9 (q : Pattern) (ha : d85590 q = 1) (hb : d107483 q = 1) : d111184 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85590, d111184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85590, d111184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7942 q = 1) (hb : d107483 q = 1) : d111189 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7942, d111189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16986 q ha hb
    | true =>
      simp only [d7942, d111189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d7943 q = 1) (hb : d107483 q = 1) : d111190 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7943, d111190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7943, d111190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d85591 q = 1) (hb : d107483 q = 1) : d111191 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85591, d111191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85591, d111191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85592 q = 1) (hb : d107483 q = 1) : d111192 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85592, d111192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85592, d111192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85593 q = 1) (hb : d107483 q = 1) : d111193 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85593, d111193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85593, d111193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d7949 q = 1) (hb : d107483 q = 1) : d111196 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7949, d111196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16990 q ha hb
    | true =>
      simp only [d7949, d111196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16988 q ha hb
  have h16 (q : Pattern) (ha : d7950 q = 1) (hb : d107483 q = 1) : d111197 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7950, d111197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7950, d111197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d7951 q = 1) (hb : d107483 q = 1) : d111198 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7951, d111198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d7951, d111198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d7952 q = 1) (hb : d107483 q = 1) : d111199 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7952, d111199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7952, d111199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d7954 q = 1) (hb : d107483 q = 1) : d111201 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7954, d111201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16991 q ha hb
    | true =>
      simp only [d7954, d111201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16989 q ha hb
  have h20 (q : Pattern) (ha : d7955 q = 1) (hb : d107483 q = 1) : d111202 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7955, d111202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7955, d111202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d7956 q = 1) (hb : d107483 q = 1) : d111203 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7956, d111203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d7956, d111203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d7958 q = 1) (hb : d107483 q = 1) : d111205 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7958, d111205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16992 q ha hb
    | true =>
      simp only [d7958, d111205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16977 q ha hb
  have h23 (q : Pattern) (ha : d85595 q = 1) (hb : d107483 q = 1) : d111206 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85595, d111206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d85595, d111206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d7963 q = 1) (hb : d107483 q = 1) : d111208 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7963, d111208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16993 q ha hb
    | true =>
      simp only [d7963, d111208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d7964 q = 1) (hb : d107483 q = 1) : d111209 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7964, d111209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d7964, d111209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d85596 q = 1) (hb : d107483 q = 1) : d111210 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85596, d111210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d85596, d111210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d85597 q = 1) (hb : d107483 q = 1) : d111211 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85597, d111211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85597, d111211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d85598 q = 1) (hb : d107483 q = 1) : d111212 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85598, d111212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d85598, d111212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d85599 q = 1) (hb : d107483 q = 1) : d111213 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85599, d111213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85599, d111213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro16995 (p : Pattern) (ha : d85606 p = 1) (hb : d107483 p = 1) : d111222 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7958 q = 1) (hb : d107483 q = 1) : d111205 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7958, d111205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16992 q ha hb
    | true =>
      simp only [d7958, d111205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16977 q ha hb
  have h2 (q : Pattern) (ha : d85595 q = 1) (hb : d107483 q = 1) : d111206 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85595, d111206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85595, d111206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7963 q = 1) (hb : d107483 q = 1) : d111208 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7963, d111208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16993 q ha hb
    | true =>
      simp only [d7963, d111208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7964 q = 1) (hb : d107483 q = 1) : d111209 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7964, d111209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7964, d111209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85596 q = 1) (hb : d107483 q = 1) : d111210 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85596, d111210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85596, d111210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85604 q = 1) (hb : d107483 q = 1) : d111220 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85604, d111220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85604, d111220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85605 q = 1) (hb : d107483 q = 1) : d111221 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85605, d111221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85605, d111221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85606 q = 1) (hb : d107483 q = 1) : d111222 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85606, d111222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85606, d111222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16996 (p : Pattern) (ha : d7984 p = 1) (hb : d107483 p = 1) : d111229 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1867 q = 1) : d1867 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1873 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1874 q = 1) (hb : d85721 q = 1) : d11805 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1874, d85721, d11805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1874, d85721, d11805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1875 q = 1) (hb : d85721 q = 1) : d11806 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1875, d11806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1875, d11806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1876 q = 1) (hb : d85721 q = 1) : d11807 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1876, d11807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1876, d11807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d1873 q = 1) : d1873 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1878 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1879 q = 1) (hb : d85721 q = 1) : d11808 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, d85721, d11808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1879, d85721, d11808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1880 q = 1) (hb : d85721 q = 1) : d11809 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, d11809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1880, d11809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1881 q = 1) (hb : d85721 q = 1) : d11810 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, d11810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1881, d11810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1882 q = 1) (hb : d85721 q = 1) : d11811 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1882, d11811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1882, d11811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7983 q = 1) (hb : d107483 q = 1) : d111228 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7983, d107483, d111228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7983, d107483, d111228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d7984 q = 1) (hb : d107483 q = 1) : d111229 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7984, d111229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d7984, d111229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro16997 (p : Pattern) (ha : d7988 p = 1) (hb : d107483 p = 1) : d111233 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1873 q = 1) : d1873 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1878 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1879 q = 1) (hb : d85721 q = 1) : d11808 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, d85721, d11808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1879, d85721, d11808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1880 q = 1) (hb : d85721 q = 1) : d11809 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, d11809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1880, d11809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1881 q = 1) (hb : d85721 q = 1) : d11810 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, d11810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1881, d11810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d1878 q = 1) : d1878 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1888 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1889 q = 1) (hb : d85721 q = 1) : d11812 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, d85721, d11812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1889, d85721, d11812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1890 q = 1) (hb : d85721 q = 1) : d11813 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, d11813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1890, d11813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1891 q = 1) (hb : d85721 q = 1) : d11814 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, d11814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1891, d11814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1892 q = 1) (hb : d85721 q = 1) : d11815 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1892, d11815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1892, d11815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7987 q = 1) (hb : d107483 q = 1) : d111232 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7987, d107483, d111232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7987, d107483, d111232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d7988 q = 1) (hb : d107483 q = 1) : d111233 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7988, d111233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d7988, d111233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro16998 (p : Pattern) (ha : d7994 p = 1) (hb : d107483 p = 1) : d111239 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7985 q = 1) (hb : d107483 q = 1) : d111230 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7985, d111230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16996 q ha hb
    | true =>
      simp only [d7985, d111230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7986 q = 1) (hb : d107483 q = 1) : d111231 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7986, d111231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7986, d111231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7989 q = 1) (hb : d107483 q = 1) : d111234 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7989, d111234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16997 q ha hb
    | true =>
      simp only [d7989, d111234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7990 q = 1) (hb : d107483 q = 1) : d111235 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7990, d111235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7990, d111235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7991 q = 1) (hb : d107483 q = 1) : d111236 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7991, d111236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7991, d111236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7992 q = 1) (hb : d107483 q = 1) : d111237 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7992, d111237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7992, d111237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7993 q = 1) (hb : d107483 q = 1) : d111238 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7993, d111238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7993, d111238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7994 q = 1) (hb : d107483 q = 1) : d111239 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7994, d111239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7994, d111239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro16999 (p : Pattern) (ha : d7998 p = 1) (hb : d107483 p = 1) : d111243 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7989 q = 1) (hb : d107483 q = 1) : d111234 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7989, d111234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16997 q ha hb
    | true =>
      simp only [d7989, d111234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7990 q = 1) (hb : d107483 q = 1) : d111235 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7990, d111235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7990, d111235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1908 q = 1) (hb : d107483 q = 1) : d11831 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, d11831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16971 q ha hb
    | true =>
      simp only [d1908, d11831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1909 q = 1) (hb : d107483 q = 1) : d11832 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, d11832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1909, d11832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7995 q = 1) (hb : d107483 q = 1) : d111240 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7995, d111240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7995, d111240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7996 q = 1) (hb : d107483 q = 1) : d111241 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7996, d111241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7996, d111241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7997 q = 1) (hb : d107483 q = 1) : d111242 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7997, d111242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7997, d111242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7998 q = 1) (hb : d107483 q = 1) : d111243 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7998, d111243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7998, d111243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
