import NetHack.Soko22Hazard87.AndIntroBlocks0012
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro3250 (p : Pattern) (ha : d54905 p = 1) (hb : d65873 p = 1) : d66004 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54900 q = 1) (hb : d65868 q = 1) : d65999 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54900, d65868, d65999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54900, d65868, d65999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3249 q ha hb
  have h2 (q : Pattern) (ha : d54901 q = 1) (hb : d65869 q = 1) : d66000 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54901, d65869, d66000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54901, d65869, d66000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54902 q = 1) (hb : d65870 q = 1) : d66001 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54902, d65870, d66001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54902, d65870, d66001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54903 q = 1) (hb : d65871 q = 1) : d66002 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54903, d65871, d66002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54903, d65871, d66002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54904 q = 1) (hb : d65872 q = 1) : d66003 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54904, d65872, d66003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54904, d65872, d66003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54905 q = 1) (hb : d65873 q = 1) : d66004 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54905, d65873, d66004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54905, d65873, d66004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3251 (p : Pattern) (ha : d1639 p = 1) (hb : d55667 p = 1) : d53764 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1624 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1624, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro216 q ha hb
    | true =>
      simp only [d1624, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
  have h2 (q : Pattern) (ha : d1625 q = 1) (hb : d53066 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d53066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1625, d53066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1626 q = 1) (hb : d53067 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d53067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1626, d53067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1627 q = 1) (hb : d53068 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, d53068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1627, d53068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1628 q = 1) (hb : d53069 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, d53069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, d53069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d1638 q = 1) : d1638 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d1639 q = 1) (hb : d55667 q = 1) : d53764 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1639, d55667, d53764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1639, d55667, d53764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro3252 (p : Pattern) (ha : d54910 p = 1) (hb : d65877 p = 1) : d66013 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55670 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1629 q = 1) : d1629 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d1640 q = 1) (hb : d55668 q = 1) : d66008 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d55668, d66008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1640, d55668, d66008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3251 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1641 q = 1) (hb : d55669 q = 1) : d66009 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d55669, d66009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1641, d55669, d66009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53762 q = 1) (hb : d55670 q = 1) : d66010 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53762, d55670, d66010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53762, d55670, d66010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d53763 q = 1) (hb : d55670 q = 1) : d66011 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53763, d66011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53763, d66011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54909 q = 1) (hb : d55670 q = 1) : d66012 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54909, d66012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54909, d66012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d54910 q = 1) (hb : d65877 q = 1) : d66013 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54910, d65877, d66013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54910, d65877, d66013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h8 p ha hb
theorem andIntro3253 (p : Pattern) (ha : d54916 p = 1) (hb : d65883 p = 1) : d66019 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54911 q = 1) (hb : d65878 q = 1) : d66014 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54911, d65878, d66014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54911, d65878, d66014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3252 q ha hb
  have h2 (q : Pattern) (ha : d54912 q = 1) (hb : d65879 q = 1) : d66015 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54912, d65879, d66015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54912, d65879, d66015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54913 q = 1) (hb : d65880 q = 1) : d66016 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54913, d65880, d66016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54913, d65880, d66016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54914 q = 1) (hb : d65881 q = 1) : d66017 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54914, d65881, d66017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54914, d65881, d66017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54915 q = 1) (hb : d65882 q = 1) : d66018 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54915, d65882, d66018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54915, d65882, d66018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54916 q = 1) (hb : d65883 q = 1) : d66019 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54916, d65883, d66019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54916, d65883, d66019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3254 (p : Pattern) (ha : d2122 p = 1) (hb : d55684 p = 1) : d53794 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2107 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2107, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro275 q ha hb
    | true =>
      simp only [d2107, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
  have h2 (q : Pattern) (ha : d2108 q = 1) (hb : d53387 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d53387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2108, d53387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2109 q = 1) (hb : d53388 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d53388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2109, d53388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2110 q = 1) (hb : d53389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, d53389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2110, d53389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2111 q = 1) (hb : d53390 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, d53390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, d53390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d2121 q = 1) : d2121 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d2122 q = 1) (hb : d55684 q = 1) : d53794 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2122, d55684, d53794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2122, d55684, d53794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro3255 (p : Pattern) (ha : d54922 p = 1) (hb : d65888 p = 1) : d66029 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55687 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2112 q = 1) : d2112 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d2123 q = 1) (hb : d55685 q = 1) : d66024 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d55685, d66024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2123, d55685, d66024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3254 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2124 q = 1) (hb : d55686 q = 1) : d66025 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d55686, d66025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2124, d55686, d66025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53792 q = 1) (hb : d55687 q = 1) : d66026 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53792, d55687, d66026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53792, d55687, d66026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d53793 q = 1) (hb : d55687 q = 1) : d66027 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53793, d66027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53793, d66027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54921 q = 1) (hb : d55687 q = 1) : d66028 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54921, d66028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54921, d66028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d54922 q = 1) (hb : d65888 q = 1) : d66029 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54922, d65888, d66029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54922, d65888, d66029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h8 p ha hb
theorem andIntro3256 (p : Pattern) (ha : d54928 p = 1) (hb : d65894 p = 1) : d66035 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54923 q = 1) (hb : d65889 q = 1) : d66030 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54923, d65889, d66030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54923, d65889, d66030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3255 q ha hb
  have h2 (q : Pattern) (ha : d54924 q = 1) (hb : d65890 q = 1) : d66031 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54924, d65890, d66031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54924, d65890, d66031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54925 q = 1) (hb : d65891 q = 1) : d66032 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54925, d65891, d66032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54925, d65891, d66032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54926 q = 1) (hb : d65892 q = 1) : d66033 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54926, d65892, d66033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54926, d65892, d66033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54927 q = 1) (hb : d65893 q = 1) : d66034 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54927, d65893, d66034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54927, d65893, d66034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54928 q = 1) (hb : d65894 q = 1) : d66035 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54928, d65894, d66035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54928, d65894, d66035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3257 (p : Pattern) (ha : d54934 p = 1) (hb : d65900 p = 1) : d66041 p = 1 := by
  have h0 (q : Pattern) (ha : d54887 q = 1) (hb : d65857 q = 1) : d65978 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54887, d65857, d65978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3241 q ha hb
    | true =>
      simp only [d54887, d65857, d65978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3244 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54896 q = 1) (hb : d65865 q = 1) : d65991 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54896, d65865, d65991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54896, d65865, d65991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3247 q ha hb
  have h3 (q : Pattern) (ha : d54897 q = 1) (hb : d65866 q = 1) : d65992 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54897, d65866, d65992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54897, d65866, d65992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54906 q = 1) (hb : d65874 q = 1) : d66005 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54906, d65874, d66005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54906, d65874, d66005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3250 q ha hb
  have h5 (q : Pattern) (ha : d54907 q = 1) (hb : d65875 q = 1) : d66006 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54907, d65875, d66006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54907, d65875, d66006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54908 q = 1) (hb : d65876 q = 1) : d66007 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54908, d65876, d66007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54908, d65876, d66007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54917 q = 1) (hb : d65884 q = 1) : d66020 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54917, d65884, d66020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54917, d65884, d66020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3253 q ha hb
  have h8 (q : Pattern) (ha : d54918 q = 1) (hb : d65885 q = 1) : d66021 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54918, d65885, d66021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54918, d65885, d66021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54919 q = 1) (hb : d65886 q = 1) : d66022 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54919, d65886, d66022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54919, d65886, d66022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54920 q = 1) (hb : d65887 q = 1) : d66023 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54920, d65887, d66023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54920, d65887, d66023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54929 q = 1) (hb : d65895 q = 1) : d66036 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54929, d65895, d66036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54929, d65895, d66036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3256 q ha hb
  have h12 (q : Pattern) (ha : d54930 q = 1) (hb : d65896 q = 1) : d66037 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54930, d65896, d66037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54930, d65896, d66037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54931 q = 1) (hb : d65897 q = 1) : d66038 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54931, d65897, d66038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54931, d65897, d66038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54932 q = 1) (hb : d65898 q = 1) : d66039 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54932, d65898, d66039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54932, d65898, d66039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54933 q = 1) (hb : d65899 q = 1) : d66040 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54933, d65899, d66040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54933, d65899, d66040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54934 q = 1) (hb : d65900 q = 1) : d66041 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d54934, d65900, d66041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54934, d65900, d66041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro3258 (p : Pattern) (ha : d54940 p = 1) (hb : d65906 p = 1) : d66047 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54935 q = 1) (hb : d65901 q = 1) : d66042 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54935, d65901, d66042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3257 q ha hb
    | true =>
      simp only [d54935, d65901, d66042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54936 q = 1) (hb : d65902 q = 1) : d66043 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54936, d65902, d66043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54936, d65902, d66043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54937 q = 1) (hb : d65903 q = 1) : d66044 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54937, d65903, d66044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54937, d65903, d66044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54938 q = 1) (hb : d65904 q = 1) : d66045 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54938, d65904, d66045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54938, d65904, d66045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54939 q = 1) (hb : d65905 q = 1) : d66046 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54939, d65905, d66046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54939, d65905, d66046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54940 q = 1) (hb : d65906 q = 1) : d66047 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d54940, d65906, d66047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54940, d65906, d66047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3259 (p : Pattern) (ha : d54946 p = 1) (hb : d65912 p = 1) : d66053 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54941 q = 1) (hb : d65907 q = 1) : d66048 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54941, d65907, d66048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3258 q ha hb
    | true =>
      simp only [d54941, d65907, d66048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54942 q = 1) (hb : d65908 q = 1) : d66049 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54942, d65908, d66049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54942, d65908, d66049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54943 q = 1) (hb : d65909 q = 1) : d66050 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54943, d65909, d66050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54943, d65909, d66050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54944 q = 1) (hb : d65910 q = 1) : d66051 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54944, d65910, d66051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54944, d65910, d66051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54945 q = 1) (hb : d65911 q = 1) : d66052 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54945, d65911, d66052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54945, d65911, d66052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54946 q = 1) (hb : d65912 q = 1) : d66053 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d54946, d65912, d66053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54946, d65912, d66053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3260 (p : Pattern) (ha : d54952 p = 1) (hb : d65918 p = 1) : d66059 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54947 q = 1) (hb : d65913 q = 1) : d66054 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54947, d65913, d66054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3259 q ha hb
    | true =>
      simp only [d54947, d65913, d66054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54948 q = 1) (hb : d65914 q = 1) : d66055 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54948, d65914, d66055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54948, d65914, d66055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54949 q = 1) (hb : d65915 q = 1) : d66056 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54949, d65915, d66056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54949, d65915, d66056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54950 q = 1) (hb : d65916 q = 1) : d66057 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54950, d65916, d66057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54950, d65916, d66057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54951 q = 1) (hb : d65917 q = 1) : d66058 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54951, d65917, d66058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54951, d65917, d66058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54952 q = 1) (hb : d65918 q = 1) : d66059 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d54952, d65918, d66059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54952, d65918, d66059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3261 (p : Pattern) (ha : d54958 p = 1) (hb : d65924 p = 1) : d66065 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54953 q = 1) (hb : d65919 q = 1) : d66060 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54953, d65919, d66060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3260 q ha hb
    | true =>
      simp only [d54953, d65919, d66060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54954 q = 1) (hb : d65920 q = 1) : d66061 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54954, d65920, d66061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54954, d65920, d66061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54955 q = 1) (hb : d65921 q = 1) : d66062 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54955, d65921, d66062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54955, d65921, d66062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54956 q = 1) (hb : d65922 q = 1) : d66063 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54956, d65922, d66063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54956, d65922, d66063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54957 q = 1) (hb : d65923 q = 1) : d66064 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54957, d65923, d66064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54957, d65923, d66064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54958 q = 1) (hb : d65924 q = 1) : d66065 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d54958, d65924, d66065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54958, d65924, d66065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3262 (p : Pattern) (ha : d54964 p = 1) (hb : d65930 p = 1) : d66071 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54959 q = 1) (hb : d65925 q = 1) : d66066 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54959, d65925, d66066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3261 q ha hb
    | true =>
      simp only [d54959, d65925, d66066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54960 q = 1) (hb : d65926 q = 1) : d66067 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54960, d65926, d66067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54960, d65926, d66067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54961 q = 1) (hb : d65927 q = 1) : d66068 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54961, d65927, d66068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54961, d65927, d66068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54962 q = 1) (hb : d65928 q = 1) : d66069 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54962, d65928, d66069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54962, d65928, d66069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54963 q = 1) (hb : d65929 q = 1) : d66070 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54963, d65929, d66070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54963, d65929, d66070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54964 q = 1) (hb : d65930 q = 1) : d66071 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d54964, d65930, d66071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54964, d65930, d66071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3263 (p : Pattern) (ha : d54970 p = 1) (hb : d65936 p = 1) : d66077 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54965 q = 1) (hb : d65931 q = 1) : d66072 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54965, d65931, d66072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3262 q ha hb
    | true =>
      simp only [d54965, d65931, d66072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54966 q = 1) (hb : d65932 q = 1) : d66073 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54966, d65932, d66073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54966, d65932, d66073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54967 q = 1) (hb : d65933 q = 1) : d66074 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54967, d65933, d66074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54967, d65933, d66074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54968 q = 1) (hb : d65934 q = 1) : d66075 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54968, d65934, d66075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54968, d65934, d66075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54969 q = 1) (hb : d65935 q = 1) : d66076 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54969, d65935, d66076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54969, d65935, d66076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54970 q = 1) (hb : d65936 q = 1) : d66077 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54970, d65936, d66077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54970, d65936, d66077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3264 (p : Pattern) (ha : d54976 p = 1) (hb : d65942 p = 1) : d66083 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54971 q = 1) (hb : d65937 q = 1) : d66078 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54971, d65937, d66078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3263 q ha hb
    | true =>
      simp only [d54971, d65937, d66078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54972 q = 1) (hb : d65938 q = 1) : d66079 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54972, d65938, d66079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54972, d65938, d66079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54973 q = 1) (hb : d65939 q = 1) : d66080 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54973, d65939, d66080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54973, d65939, d66080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54974 q = 1) (hb : d65940 q = 1) : d66081 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54974, d65940, d66081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54974, d65940, d66081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54975 q = 1) (hb : d65941 q = 1) : d66082 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54975, d65941, d66082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54975, d65941, d66082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54976 q = 1) (hb : d65942 q = 1) : d66083 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54976, d65942, d66083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54976, d65942, d66083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3265 (p : Pattern) (ha : d54865 p = 1) (hb : d65731 p = 1) : d62704 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2527 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2527 q = 1) (hb : d53637 q = 1) : d2527 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2527 q = 1) (hb : d53638 q = 1) : d62702 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, d62702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53638, d62702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2527 q = 1) (hb : d54864 q = 1) : d62703 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54864, d62703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54864, d62703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d54865 q = 1) (hb : d65731 q = 1) : d62704 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54865, d65731, d62704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d54865, d65731, d62704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro3266 (p : Pattern) (ha : d54872 p = 1) (hb : d65737 p = 1) : d62712 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2539 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2539 q = 1) (hb : d53653 q = 1) : d2539 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2539 q = 1) (hb : d53654 q = 1) : d62710 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, d62710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53654, d62710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2539 q = 1) (hb : d54871 q = 1) : d62711 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54871, d62711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54871, d62711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d54872 q = 1) (hb : d65737 q = 1) : d62712 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54872, d65737, d62712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d54872, d65737, d62712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro3267 (p : Pattern) (ha : d54878 p = 1) (hb : d65743 p = 1) : d62718 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54866 q = 1) (hb : d65732 q = 1) : d62705 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54866, d65732, d62705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54866, d65732, d62705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3265 q ha hb
  have h2 (q : Pattern) (ha : d54867 q = 1) (hb : d65733 q = 1) : d62706 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54867, d65733, d62706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54867, d65733, d62706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54868 q = 1) (hb : d65734 q = 1) : d62707 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54868, d65734, d62707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54868, d65734, d62707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54869 q = 1) (hb : d65735 q = 1) : d62708 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54869, d65735, d62708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54869, d65735, d62708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54870 q = 1) (hb : d65736 q = 1) : d62709 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54870, d65736, d62709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54870, d65736, d62709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54873 q = 1) (hb : d65738 q = 1) : d62713 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54873, d65738, d62713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54873, d65738, d62713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3266 q ha hb
  have h7 (q : Pattern) (ha : d54874 q = 1) (hb : d65739 q = 1) : d62714 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54874, d65739, d62714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54874, d65739, d62714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54875 q = 1) (hb : d65740 q = 1) : d62715 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54875, d65740, d62715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54875, d65740, d62715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54876 q = 1) (hb : d65741 q = 1) : d62716 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54876, d65741, d62716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54876, d65741, d62716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54877 q = 1) (hb : d65742 q = 1) : d62717 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54877, d65742, d62717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54877, d65742, d62717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54878 q = 1) (hb : d65743 q = 1) : d62718 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54878, d65743, d62718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54878, d65743, d62718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro3268 (p : Pattern) (ha : d54880 p = 1) (hb : d65744 p = 1) : d62721 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2552 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2552 q = 1) (hb : d53678 q = 1) : d2552 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2552 q = 1) (hb : d53679 q = 1) : d62719 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53679, d62719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53679, d62719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2552 q = 1) (hb : d54879 q = 1) : d62720 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54879, d62720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54879, d62720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d54880 q = 1) (hb : d65744 q = 1) : d62721 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54880, d65744, d62721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d54880, d65744, d62721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro3269 (p : Pattern) (ha : d54886 p = 1) (hb : d65750 p = 1) : d62727 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54881 q = 1) (hb : d65745 q = 1) : d62722 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54881, d65745, d62722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54881, d65745, d62722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3268 q ha hb
  have h2 (q : Pattern) (ha : d54882 q = 1) (hb : d65746 q = 1) : d62723 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54882, d65746, d62723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54882, d65746, d62723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54883 q = 1) (hb : d65747 q = 1) : d62724 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54883, d65747, d62724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54883, d65747, d62724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54884 q = 1) (hb : d65748 q = 1) : d62725 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54884, d65748, d62725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54884, d65748, d62725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54885 q = 1) (hb : d65749 q = 1) : d62726 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54885, d65749, d62726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54885, d65749, d62726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54886 q = 1) (hb : d65750 q = 1) : d62727 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54886, d65750, d62727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54886, d65750, d62727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3270 (p : Pattern) (ha : d54889 p = 1) (hb : d65752 p = 1) : d62731 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2566 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2566 q = 1) (hb : d53705 q = 1) : d2566 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2566 q = 1) (hb : d53706 q = 1) : d62729 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53706, d62729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53706, d62729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2566 q = 1) (hb : d54888 q = 1) : d62730 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54888, d62730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54888, d62730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d54889 q = 1) (hb : d65752 q = 1) : d62731 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54889, d65752, d62731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d54889, d65752, d62731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro3271 (p : Pattern) (ha : d54895 p = 1) (hb : d65758 p = 1) : d62737 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54890 q = 1) (hb : d65753 q = 1) : d62732 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54890, d65753, d62732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54890, d65753, d62732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3270 q ha hb
  have h2 (q : Pattern) (ha : d54891 q = 1) (hb : d65754 q = 1) : d62733 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54891, d65754, d62733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54891, d65754, d62733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54892 q = 1) (hb : d65755 q = 1) : d62734 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54892, d65755, d62734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54892, d65755, d62734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54893 q = 1) (hb : d65756 q = 1) : d62735 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54893, d65756, d62735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54893, d65756, d62735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54894 q = 1) (hb : d65757 q = 1) : d62736 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54894, d65757, d62736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54894, d65757, d62736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54895 q = 1) (hb : d65758 q = 1) : d62737 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54895, d65758, d62737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54895, d65758, d62737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3272 (p : Pattern) (ha : d54899 p = 1) (hb : d65761 p = 1) : d62742 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2581 q = 1) (hb : d53733 q = 1) : d2581 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2581 q = 1) (hb : d53734 q = 1) : d62740 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53734, d62740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53734, d62740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2581 q = 1) (hb : d54898 q = 1) : d62741 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54898, d62741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54898, d62741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d54899 q = 1) (hb : d65761 q = 1) : d62742 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54899, d65761, d62742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d54899, d65761, d62742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro3273 (p : Pattern) (ha : d54905 p = 1) (hb : d65767 p = 1) : d62748 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54900 q = 1) (hb : d65762 q = 1) : d62743 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54900, d65762, d62743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54900, d65762, d62743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3272 q ha hb
  have h2 (q : Pattern) (ha : d54901 q = 1) (hb : d65763 q = 1) : d62744 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54901, d65763, d62744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54901, d65763, d62744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54902 q = 1) (hb : d65764 q = 1) : d62745 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54902, d65764, d62745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54902, d65764, d62745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54903 q = 1) (hb : d65765 q = 1) : d62746 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54903, d65765, d62746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54903, d65765, d62746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54904 q = 1) (hb : d65766 q = 1) : d62747 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54904, d65766, d62747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54904, d65766, d62747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54905 q = 1) (hb : d65767 q = 1) : d62748 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54905, d65767, d62748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54905, d65767, d62748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3274 (p : Pattern) (ha : d54910 p = 1) (hb : d65771 p = 1) : d62754 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2597 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2597 q = 1) (hb : d53762 q = 1) : d2597 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2597 q = 1) (hb : d53763 q = 1) : d62752 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53763, d62752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53763, d62752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2597 q = 1) (hb : d54909 q = 1) : d62753 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54909, d62753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54909, d62753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d54910 q = 1) (hb : d65771 q = 1) : d62754 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54910, d65771, d62754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d54910, d65771, d62754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro3275 (p : Pattern) (ha : d54916 p = 1) (hb : d65777 p = 1) : d62760 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54911 q = 1) (hb : d65772 q = 1) : d62755 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54911, d65772, d62755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54911, d65772, d62755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3274 q ha hb
  have h2 (q : Pattern) (ha : d54912 q = 1) (hb : d65773 q = 1) : d62756 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54912, d65773, d62756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54912, d65773, d62756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54913 q = 1) (hb : d65774 q = 1) : d62757 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54913, d65774, d62757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54913, d65774, d62757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54914 q = 1) (hb : d65775 q = 1) : d62758 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54914, d65775, d62758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54914, d65775, d62758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54915 q = 1) (hb : d65776 q = 1) : d62759 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54915, d65776, d62759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54915, d65776, d62759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54916 q = 1) (hb : d65777 q = 1) : d62760 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54916, d65777, d62760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54916, d65777, d62760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3276 (p : Pattern) (ha : d54922 p = 1) (hb : d65782 p = 1) : d62767 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2614 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2614 q = 1) (hb : d53792 q = 1) : d2614 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2614 q = 1) (hb : d53793 q = 1) : d62765 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53793, d62765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53793, d62765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2614 q = 1) (hb : d54921 q = 1) : d62766 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54921, d62766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54921, d62766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d54922 q = 1) (hb : d65782 q = 1) : d62767 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54922, d65782, d62767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d54922, d65782, d62767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro3277 (p : Pattern) (ha : d54928 p = 1) (hb : d65788 p = 1) : d62773 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54923 q = 1) (hb : d65783 q = 1) : d62768 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54923, d65783, d62768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54923, d65783, d62768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3276 q ha hb
  have h2 (q : Pattern) (ha : d54924 q = 1) (hb : d65784 q = 1) : d62769 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54924, d65784, d62769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54924, d65784, d62769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54925 q = 1) (hb : d65785 q = 1) : d62770 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54925, d65785, d62770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54925, d65785, d62770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54926 q = 1) (hb : d65786 q = 1) : d62771 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54926, d65786, d62771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54926, d65786, d62771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54927 q = 1) (hb : d65787 q = 1) : d62772 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54927, d65787, d62772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54927, d65787, d62772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54928 q = 1) (hb : d65788 q = 1) : d62773 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54928, d65788, d62773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54928, d65788, d62773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3278 (p : Pattern) (ha : d54934 p = 1) (hb : d65794 p = 1) : d62779 p = 1 := by
  have h0 (q : Pattern) (ha : d54887 q = 1) (hb : d65751 q = 1) : d62728 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54887, d65751, d62728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3267 q ha hb
    | true =>
      simp only [d54887, d65751, d62728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3269 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54896 q = 1) (hb : d65759 q = 1) : d62738 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54896, d65759, d62738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54896, d65759, d62738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3271 q ha hb
  have h3 (q : Pattern) (ha : d54897 q = 1) (hb : d65760 q = 1) : d62739 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54897, d65760, d62739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54897, d65760, d62739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54906 q = 1) (hb : d65768 q = 1) : d62749 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54906, d65768, d62749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54906, d65768, d62749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3273 q ha hb
  have h5 (q : Pattern) (ha : d54907 q = 1) (hb : d65769 q = 1) : d62750 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54907, d65769, d62750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54907, d65769, d62750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54908 q = 1) (hb : d65770 q = 1) : d62751 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54908, d65770, d62751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54908, d65770, d62751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54917 q = 1) (hb : d65778 q = 1) : d62761 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54917, d65778, d62761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54917, d65778, d62761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3275 q ha hb
  have h8 (q : Pattern) (ha : d54918 q = 1) (hb : d65779 q = 1) : d62762 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54918, d65779, d62762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54918, d65779, d62762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54919 q = 1) (hb : d65780 q = 1) : d62763 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54919, d65780, d62763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54919, d65780, d62763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54920 q = 1) (hb : d65781 q = 1) : d62764 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54920, d65781, d62764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54920, d65781, d62764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54929 q = 1) (hb : d65789 q = 1) : d62774 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54929, d65789, d62774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54929, d65789, d62774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3277 q ha hb
  have h12 (q : Pattern) (ha : d54930 q = 1) (hb : d65790 q = 1) : d62775 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54930, d65790, d62775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54930, d65790, d62775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54931 q = 1) (hb : d65791 q = 1) : d62776 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54931, d65791, d62776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54931, d65791, d62776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54932 q = 1) (hb : d65792 q = 1) : d62777 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54932, d65792, d62777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54932, d65792, d62777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54933 q = 1) (hb : d65793 q = 1) : d62778 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54933, d65793, d62778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54933, d65793, d62778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54934 q = 1) (hb : d65794 q = 1) : d62779 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d54934, d65794, d62779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54934, d65794, d62779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro3279 (p : Pattern) (ha : d54940 p = 1) (hb : d65800 p = 1) : d62785 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54935 q = 1) (hb : d65795 q = 1) : d62780 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54935, d65795, d62780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3278 q ha hb
    | true =>
      simp only [d54935, d65795, d62780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54936 q = 1) (hb : d65796 q = 1) : d62781 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54936, d65796, d62781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54936, d65796, d62781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54937 q = 1) (hb : d65797 q = 1) : d62782 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54937, d65797, d62782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54937, d65797, d62782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54938 q = 1) (hb : d65798 q = 1) : d62783 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54938, d65798, d62783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54938, d65798, d62783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54939 q = 1) (hb : d65799 q = 1) : d62784 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54939, d65799, d62784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54939, d65799, d62784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54940 q = 1) (hb : d65800 q = 1) : d62785 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d54940, d65800, d62785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54940, d65800, d62785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3280 (p : Pattern) (ha : d54946 p = 1) (hb : d65806 p = 1) : d62791 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54941 q = 1) (hb : d65801 q = 1) : d62786 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54941, d65801, d62786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3279 q ha hb
    | true =>
      simp only [d54941, d65801, d62786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54942 q = 1) (hb : d65802 q = 1) : d62787 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54942, d65802, d62787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54942, d65802, d62787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54943 q = 1) (hb : d65803 q = 1) : d62788 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54943, d65803, d62788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54943, d65803, d62788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54944 q = 1) (hb : d65804 q = 1) : d62789 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54944, d65804, d62789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54944, d65804, d62789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54945 q = 1) (hb : d65805 q = 1) : d62790 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54945, d65805, d62790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54945, d65805, d62790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54946 q = 1) (hb : d65806 q = 1) : d62791 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d54946, d65806, d62791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54946, d65806, d62791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3281 (p : Pattern) (ha : d54952 p = 1) (hb : d65812 p = 1) : d62797 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54947 q = 1) (hb : d65807 q = 1) : d62792 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54947, d65807, d62792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3280 q ha hb
    | true =>
      simp only [d54947, d65807, d62792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54948 q = 1) (hb : d65808 q = 1) : d62793 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54948, d65808, d62793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54948, d65808, d62793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54949 q = 1) (hb : d65809 q = 1) : d62794 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54949, d65809, d62794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54949, d65809, d62794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54950 q = 1) (hb : d65810 q = 1) : d62795 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54950, d65810, d62795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54950, d65810, d62795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54951 q = 1) (hb : d65811 q = 1) : d62796 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54951, d65811, d62796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54951, d65811, d62796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54952 q = 1) (hb : d65812 q = 1) : d62797 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d54952, d65812, d62797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54952, d65812, d62797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3282 (p : Pattern) (ha : d54958 p = 1) (hb : d65818 p = 1) : d62803 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54953 q = 1) (hb : d65813 q = 1) : d62798 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54953, d65813, d62798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3281 q ha hb
    | true =>
      simp only [d54953, d65813, d62798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54954 q = 1) (hb : d65814 q = 1) : d62799 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54954, d65814, d62799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54954, d65814, d62799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54955 q = 1) (hb : d65815 q = 1) : d62800 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54955, d65815, d62800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54955, d65815, d62800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54956 q = 1) (hb : d65816 q = 1) : d62801 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54956, d65816, d62801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54956, d65816, d62801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54957 q = 1) (hb : d65817 q = 1) : d62802 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54957, d65817, d62802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54957, d65817, d62802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54958 q = 1) (hb : d65818 q = 1) : d62803 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d54958, d65818, d62803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54958, d65818, d62803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3283 (p : Pattern) (ha : d54964 p = 1) (hb : d65824 p = 1) : d62809 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54959 q = 1) (hb : d65819 q = 1) : d62804 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54959, d65819, d62804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3282 q ha hb
    | true =>
      simp only [d54959, d65819, d62804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54960 q = 1) (hb : d65820 q = 1) : d62805 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54960, d65820, d62805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54960, d65820, d62805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54961 q = 1) (hb : d65821 q = 1) : d62806 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54961, d65821, d62806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54961, d65821, d62806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54962 q = 1) (hb : d65822 q = 1) : d62807 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54962, d65822, d62807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54962, d65822, d62807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54963 q = 1) (hb : d65823 q = 1) : d62808 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54963, d65823, d62808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54963, d65823, d62808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54964 q = 1) (hb : d65824 q = 1) : d62809 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d54964, d65824, d62809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54964, d65824, d62809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3284 (p : Pattern) (ha : d54970 p = 1) (hb : d65830 p = 1) : d62815 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54965 q = 1) (hb : d65825 q = 1) : d62810 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54965, d65825, d62810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3283 q ha hb
    | true =>
      simp only [d54965, d65825, d62810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54966 q = 1) (hb : d65826 q = 1) : d62811 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54966, d65826, d62811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54966, d65826, d62811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54967 q = 1) (hb : d65827 q = 1) : d62812 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54967, d65827, d62812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54967, d65827, d62812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54968 q = 1) (hb : d65828 q = 1) : d62813 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54968, d65828, d62813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54968, d65828, d62813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54969 q = 1) (hb : d65829 q = 1) : d62814 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54969, d65829, d62814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54969, d65829, d62814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54970 q = 1) (hb : d65830 q = 1) : d62815 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54970, d65830, d62815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54970, d65830, d62815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3285 (p : Pattern) (ha : d54976 p = 1) (hb : d65836 p = 1) : d62821 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54971 q = 1) (hb : d65831 q = 1) : d62816 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54971, d65831, d62816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3284 q ha hb
    | true =>
      simp only [d54971, d65831, d62816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54972 q = 1) (hb : d65832 q = 1) : d62817 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54972, d65832, d62817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54972, d65832, d62817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54973 q = 1) (hb : d65833 q = 1) : d62818 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54973, d65833, d62818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54973, d65833, d62818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54974 q = 1) (hb : d65834 q = 1) : d62819 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54974, d65834, d62819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54974, d65834, d62819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54975 q = 1) (hb : d65835 q = 1) : d62820 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54975, d65835, d62820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54975, d65835, d62820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54976 q = 1) (hb : d65836 q = 1) : d62821 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54976, d65836, d62821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54976, d65836, d62821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3286 (p : Pattern) (ha : d56141 p = 1) (hb : d57566 p = 1) : d56141 p = 1 := by
  have h0 (q : Pattern) (ha : d56141 q = 1) (hb : d57566 q = 1) : d56141 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro3287 (p : Pattern) (ha : d55894 p = 1) (hb : d56141 p = 1) : d56141 p = 1 := by
  have h0 (q : Pattern) (ha : d55894 q = 1) (hb : d56141 q = 1) : d56141 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro3288 (p : Pattern) (ha : d48 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d45 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d47 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d48 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d48, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d48, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro3289 (p : Pattern) (ha : d55 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d45 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d47 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d54 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d55 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d55, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d55, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro3290 (p : Pattern) (ha : d2520 p = 1) (hb : d66088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3288 q ha hb
    | true =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3289 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d57 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d58 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d59 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2519 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2520 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro3291 (p : Pattern) (ha : d104 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d101 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d102 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d103 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d104 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro3292 (p : Pattern) (ha : d213 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d101 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d102 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d103 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d213 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h5 p ha hb
theorem andIntro3293 (p : Pattern) (ha : d51643 p = 1) (hb : d56773 p = 1) : d3845 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d119 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d120 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d126 q = 1) : d126 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d4336 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d51641 q = 1) (hb : d56773 q = 1) : d3843 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d56773, d3843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d51641, d56773, d3843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d51642 q = 1) (hb : d56773 q = 1) : d3844 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d3844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51642, d3844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51643 q = 1) (hb : d56773 q = 1) : d3845 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51643, d3845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51643, d3845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro3294 (p : Pattern) (ha : d51646 p = 1) (hb : d56773 p = 1) : d3848 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d119 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d120 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d126 q = 1) : d126 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d4336 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51641 q = 1) (hb : d56773 q = 1) : d3843 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d56773, d3843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d51641, d56773, d3843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d51642 q = 1) (hb : d56773 q = 1) : d3844 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d3844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51642, d3844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d197 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d198 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d202 q = 1) : d202 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d4341 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d51644 q = 1) (hb : d56773 q = 1) : d3846 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51644, d56773, d3846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d51644, d56773, d3846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d51645 q = 1) (hb : d56773 q = 1) : d3847 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51645, d3847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51645, d3847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d51646 q = 1) (hb : d56773 q = 1) : d3848 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51646, d3848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51646, d3848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro3295 (p : Pattern) (ha : d56024 p = 1) (hb : d66088 p = 1) : d3854 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3291 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3016 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3016, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3016, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51647 q = 1) (hb : d56773 q = 1) : d3849 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51647, d3849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3293 q ha hb
    | true =>
      simp only [d51647, d3849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3294 q ha hb
  have h6 (q : Pattern) (ha : d214 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3292 q ha hb
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d51648 q = 1) (hb : d56773 q = 1) : d3850 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51648, d3850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51648, d3850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51649 q = 1) (hb : d66088 q = 1) : d3851 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51649, d66088, d3851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51649, d66088, d3851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d56022 q = 1) (hb : d66088 q = 1) : d3852 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56022, d3852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d56022, d3852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2525 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3292 q ha hb
  have h11 (q : Pattern) (ha : d2526 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d2527 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2527, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2527, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d2528 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d56023 q = 1) (hb : d66088 q = 1) : d3853 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d56023, d3853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d56023, d3853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d56024 q = 1) (hb : d66088 q = 1) : d3854 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d56024, d3854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d56024, d3854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h16 p ha hb
theorem andIntro3296 (p : Pattern) (ha : d111 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d101 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d102 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d103 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d108 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d109 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d110 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d111 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro3297 (p : Pattern) (ha : d284 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d281 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d282 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d282, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d283 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d284 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro3298 (p : Pattern) (ha : d397 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d281 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d282 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d282, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d283 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d101 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d102 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d397 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro3299 (p : Pattern) (ha : d2536 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d281 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d282 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d282, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d283 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2536 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h5 p ha hb
theorem andIntro3300 (p : Pattern) (ha : d51660 p = 1) (hb : d56773 p = 1) : d3862 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d299 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d300 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d300, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d306 q = 1) : d306 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d4372 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d51658 q = 1) (hb : d56773 q = 1) : d3860 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51658, d56773, d3860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d51658, d56773, d3860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d51659 q = 1) (hb : d56773 q = 1) : d3861 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51659, d3861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51659, d3861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51660 q = 1) (hb : d56773 q = 1) : d3862 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51660, d3862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51660, d3862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro3301 (p : Pattern) (ha : d51663 p = 1) (hb : d56773 p = 1) : d3865 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d299 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d300 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d306 q = 1) : d306 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d4372 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51658 q = 1) (hb : d56773 q = 1) : d3860 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51658, d56773, d3860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d51658, d56773, d3860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d51659 q = 1) (hb : d56773 q = 1) : d3861 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51659, d3861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51659, d3861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d379 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d380 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d380, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d380, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d384 q = 1) : d384 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d4377 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d51661 q = 1) (hb : d56773 q = 1) : d3863 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51661, d56773, d3863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d51661, d56773, d3863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d51662 q = 1) (hb : d56773 q = 1) : d3864 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51662, d3864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51662, d3864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d51663 q = 1) (hb : d56773 q = 1) : d3865 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51663, d3865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51663, d3865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro3302 (p : Pattern) (ha : d56032 p = 1) (hb : d66088 p = 1) : d3871 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3297 q ha hb
  have h2 (q : Pattern) (ha : d286 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3025 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3025, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3025, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51664 q = 1) (hb : d56773 q = 1) : d3866 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51664, d3866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3300 q ha hb
    | true =>
      simp only [d51664, d3866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3301 q ha hb
  have h6 (q : Pattern) (ha : d398 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3298 q ha hb
    | true =>
      simp only [d398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3296 q ha hb
  have h7 (q : Pattern) (ha : d51665 q = 1) (hb : d56773 q = 1) : d3867 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51665, d3867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51665, d3867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51666 q = 1) (hb : d66088 q = 1) : d3868 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51666, d66088, d3868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51666, d66088, d3868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d56030 q = 1) (hb : d66088 q = 1) : d3869 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56030, d3869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d56030, d3869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2537 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3299 q ha hb
  have h11 (q : Pattern) (ha : d2538 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d2539 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2539, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2539, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d2540 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d56031 q = 1) (hb : d66088 q = 1) : d3870 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d56031, d3870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d56031, d3870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d56032 q = 1) (hb : d66088 q = 1) : d3871 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d56032, d3871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d56032, d3871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h16 p ha hb
theorem andIntro3303 (p : Pattern) (ha : d56038 p = 1) (hb : d66088 p = 1) : d3877 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2521 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3290 q ha hb
  have h2 (q : Pattern) (ha : d2522 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2523 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2524 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d56025 q = 1) (hb : d66088 q = 1) : d3855 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d56025, d3855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56025, d3855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3295 q ha hb
  have h6 (q : Pattern) (ha : d56026 q = 1) (hb : d66088 q = 1) : d3856 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d56026, d3856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56026, d3856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d56027 q = 1) (hb : d66088 q = 1) : d3857 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d56027, d3857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56027, d3857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d56028 q = 1) (hb : d66088 q = 1) : d3858 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d56028, d3858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56028, d3858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d56029 q = 1) (hb : d66088 q = 1) : d3859 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d56029, d3859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d56029, d3859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d56033 q = 1) (hb : d66088 q = 1) : d3872 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d56033, d3872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56033, d3872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3302 q ha hb
  have h11 (q : Pattern) (ha : d56034 q = 1) (hb : d66088 q = 1) : d3873 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d56034, d3873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56034, d3873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d56035 q = 1) (hb : d66088 q = 1) : d3874 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d56035, d3874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56035, d3874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d56036 q = 1) (hb : d66088 q = 1) : d3875 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d56036, d3875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56036, d3875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d56037 q = 1) (hb : d66088 q = 1) : d3876 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d56037, d3876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56037, d3876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d56038 q = 1) (hb : d66088 q = 1) : d3877 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d56038, d3877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d56038, d3877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro3304 (p : Pattern) (ha : d497 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d494 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d495 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d495, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d496 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d497 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro3305 (p : Pattern) (ha : d638 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d494 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d495 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d495, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d496 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d635 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d636 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d636, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d637 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d638 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro3306 (p : Pattern) (ha : d644 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d635 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d636 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d636, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d637 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d641 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d642 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d642, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d643 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d644 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro3307 (p : Pattern) (ha : d2549 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d494 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d495 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d495, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d496 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2549 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h5 p ha hb
theorem andIntro3308 (p : Pattern) (ha : d51685 p = 1) (hb : d56773 p = 1) : d3880 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d517 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d518 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d518, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d518, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d527 q = 1) : d527 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d4409 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d51683 q = 1) (hb : d56773 q = 1) : d3878 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51683, d56773, d3878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d51683, d56773, d3878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d51684 q = 1) (hb : d56773 q = 1) : d3879 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51684, d3879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51684, d3879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51685 q = 1) (hb : d56773 q = 1) : d3880 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51685, d3880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51685, d3880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro3309 (p : Pattern) (ha : d51688 p = 1) (hb : d56773 p = 1) : d3883 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d517 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d518 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d518, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d518, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d527 q = 1) : d527 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d4409 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51683 q = 1) (hb : d56773 q = 1) : d3878 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51683, d56773, d3878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d51683, d56773, d3878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d51684 q = 1) (hb : d56773 q = 1) : d3879 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51684, d3879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51684, d3879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d613 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d614 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d614, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d614, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d619 q = 1) : d619 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d4414 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d51686 q = 1) (hb : d56773 q = 1) : d3881 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51686, d56773, d3881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d51686, d56773, d3881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d51687 q = 1) (hb : d56773 q = 1) : d3882 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51687, d3882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51687, d3882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d51688 q = 1) (hb : d56773 q = 1) : d3883 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51688, d3883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51688, d3883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro3310 (p : Pattern) (ha : d56041 p = 1) (hb : d66088 p = 1) : d3889 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d498 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3304 q ha hb
  have h2 (q : Pattern) (ha : d499 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3035 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3035, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3035, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51689 q = 1) (hb : d56773 q = 1) : d3884 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51689, d3884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3308 q ha hb
    | true =>
      simp only [d51689, d3884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3309 q ha hb
  have h6 (q : Pattern) (ha : d645 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3305 q ha hb
    | true =>
      simp only [d645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3306 q ha hb
  have h7 (q : Pattern) (ha : d51690 q = 1) (hb : d56773 q = 1) : d3885 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51690, d3885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51690, d3885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51691 q = 1) (hb : d66088 q = 1) : d3886 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51691, d66088, d3886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51691, d66088, d3886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d56039 q = 1) (hb : d66088 q = 1) : d3887 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56039, d3887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d56039, d3887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2550 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3307 q ha hb
  have h11 (q : Pattern) (ha : d2551 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d2552 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2552, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2552, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d2553 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d56040 q = 1) (hb : d66088 q = 1) : d3888 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d56040, d3888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d56040, d3888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d56041 q = 1) (hb : d66088 q = 1) : d3889 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d56041, d3889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d56041, d3889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h16 p ha hb
theorem andIntro3311 (p : Pattern) (ha : d56047 p = 1) (hb : d66088 p = 1) : d3895 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56042 q = 1) (hb : d66088 q = 1) : d3890 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d56042, d3890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56042, d3890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3310 q ha hb
  have h2 (q : Pattern) (ha : d56043 q = 1) (hb : d66088 q = 1) : d3891 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d56043, d3891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56043, d3891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d56044 q = 1) (hb : d66088 q = 1) : d3892 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d56044, d3892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56044, d3892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d56045 q = 1) (hb : d66088 q = 1) : d3893 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d56045, d3893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56045, d3893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d56046 q = 1) (hb : d66088 q = 1) : d3894 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d56046, d3894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56046, d3894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d56047 q = 1) (hb : d66088 q = 1) : d3895 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d56047, d3895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56047, d3895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3312 (p : Pattern) (ha : d789 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d786 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d787 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d787, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d788 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d789 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro3313 (p : Pattern) (ha : d944 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d786 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d787 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d787, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d788 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d941 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d942 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d942, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d943 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d944 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro3314 (p : Pattern) (ha : d950 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d941 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d942 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d942, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d943 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d947 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d948 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d948, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d949 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d950 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro3315 (p : Pattern) (ha : d2563 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d786 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d787 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d787, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d788 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2563 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h5 p ha hb
theorem andIntro3316 (p : Pattern) (ha : d51711 p = 1) (hb : d56773 p = 1) : d3899 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d809 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d810 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d810, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d810, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d819 q = 1) : d819 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d4447 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d51709 q = 1) (hb : d56773 q = 1) : d3897 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51709, d56773, d3897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d51709, d56773, d3897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d51710 q = 1) (hb : d56773 q = 1) : d3898 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51710, d3898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51710, d3898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51711 q = 1) (hb : d56773 q = 1) : d3899 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51711, d3899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51711, d3899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro3317 (p : Pattern) (ha : d51714 p = 1) (hb : d56773 p = 1) : d3902 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d809 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d810 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d810, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d810, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d819 q = 1) : d819 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d4447 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51709 q = 1) (hb : d56773 q = 1) : d3897 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51709, d56773, d3897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d51709, d56773, d3897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d51710 q = 1) (hb : d56773 q = 1) : d3898 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51710, d3898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51710, d3898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d919 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d920 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d920, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d920, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d925 q = 1) : d925 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d4452 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d51712 q = 1) (hb : d56773 q = 1) : d3900 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51712, d56773, d3900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d51712, d56773, d3900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d51713 q = 1) (hb : d56773 q = 1) : d3901 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51713, d3901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51713, d3901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d51714 q = 1) (hb : d56773 q = 1) : d3902 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51714, d3902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51714, d3902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro3318 (p : Pattern) (ha : d56051 p = 1) (hb : d66088 p = 1) : d3908 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d790 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3312 q ha hb
  have h2 (q : Pattern) (ha : d791 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3046 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3046, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3046, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51715 q = 1) (hb : d56773 q = 1) : d3903 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51715, d3903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3316 q ha hb
    | true =>
      simp only [d51715, d3903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3317 q ha hb
  have h6 (q : Pattern) (ha : d951 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3313 q ha hb
    | true =>
      simp only [d951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3314 q ha hb
  have h7 (q : Pattern) (ha : d51716 q = 1) (hb : d56773 q = 1) : d3904 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51716, d3904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51716, d3904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51717 q = 1) (hb : d66088 q = 1) : d3905 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51717, d66088, d3905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51717, d66088, d3905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d56049 q = 1) (hb : d66088 q = 1) : d3906 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56049, d3906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d56049, d3906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2564 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3315 q ha hb
  have h11 (q : Pattern) (ha : d2565 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d2566 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2566, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2566, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d2567 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d56050 q = 1) (hb : d66088 q = 1) : d3907 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d56050, d3907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d56050, d3907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d56051 q = 1) (hb : d66088 q = 1) : d3908 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d56051, d3908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d56051, d3908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h16 p ha hb
theorem andIntro3319 (p : Pattern) (ha : d56057 p = 1) (hb : d66088 p = 1) : d3914 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56052 q = 1) (hb : d66088 q = 1) : d3909 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d56052, d3909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56052, d3909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3318 q ha hb
  have h2 (q : Pattern) (ha : d56053 q = 1) (hb : d66088 q = 1) : d3910 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d56053, d3910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56053, d3910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d56054 q = 1) (hb : d66088 q = 1) : d3911 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d56054, d3911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56054, d3911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d56055 q = 1) (hb : d66088 q = 1) : d3912 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d56055, d3912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56055, d3912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d56056 q = 1) (hb : d66088 q = 1) : d3913 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d56056, d3913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56056, d3913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d56057 q = 1) (hb : d66088 q = 1) : d3914 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d56057, d3914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56057, d3914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3320 (p : Pattern) (ha : d1168 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1165 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1166 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1166, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1167 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1168 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro3321 (p : Pattern) (ha : d1355 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1165 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1166 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1166, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1167 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1352 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1353 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1353, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d1354 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1355 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro3322 (p : Pattern) (ha : d1361 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1352 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1353 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1353, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1354 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1358 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1359 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1359, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1359, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d1360 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1361 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro3323 (p : Pattern) (ha : d2578 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1165 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1166 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1166, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1167 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2578 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h5 p ha hb
theorem andIntro3324 (p : Pattern) (ha : d51738 p = 1) (hb : d56773 p = 1) : d3919 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1188 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1189 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1189, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d1198 q = 1) : d1198 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d4486 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d51736 q = 1) (hb : d56773 q = 1) : d3917 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51736, d56773, d3917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d51736, d56773, d3917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d51737 q = 1) (hb : d56773 q = 1) : d3918 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51737, d3918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51737, d3918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51738 q = 1) (hb : d56773 q = 1) : d3919 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51738, d3919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51738, d3919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro3325 (p : Pattern) (ha : d51741 p = 1) (hb : d56773 p = 1) : d3922 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1188 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1189 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1189, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d1198 q = 1) : d1198 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d4486 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51736 q = 1) (hb : d56773 q = 1) : d3917 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51736, d56773, d3917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d51736, d56773, d3917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d51737 q = 1) (hb : d56773 q = 1) : d3918 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51737, d3918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51737, d3918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1330 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1331 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1331, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1331, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d1336 q = 1) : d1336 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d4491 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d51739 q = 1) (hb : d56773 q = 1) : d3920 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51739, d56773, d3920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d51739, d56773, d3920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d51740 q = 1) (hb : d56773 q = 1) : d3921 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51740, d3921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51740, d3921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d51741 q = 1) (hb : d56773 q = 1) : d3922 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51741, d3922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51741, d3922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro3326 (p : Pattern) (ha : d56062 p = 1) (hb : d66088 p = 1) : d3928 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1169 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3320 q ha hb
  have h2 (q : Pattern) (ha : d1170 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3058 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3058, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3058, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51742 q = 1) (hb : d56773 q = 1) : d3923 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51742, d3923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3324 q ha hb
    | true =>
      simp only [d51742, d3923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3325 q ha hb
  have h6 (q : Pattern) (ha : d1362 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3321 q ha hb
    | true =>
      simp only [d1362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3322 q ha hb
  have h7 (q : Pattern) (ha : d51743 q = 1) (hb : d56773 q = 1) : d3924 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51743, d3924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51743, d3924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51744 q = 1) (hb : d66088 q = 1) : d3925 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51744, d66088, d3925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51744, d66088, d3925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d56060 q = 1) (hb : d66088 q = 1) : d3926 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56060, d3926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d56060, d3926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2579 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3323 q ha hb
  have h11 (q : Pattern) (ha : d2580 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d2581 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2581, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2581, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d2582 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d56061 q = 1) (hb : d66088 q = 1) : d3927 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d56061, d3927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d56061, d3927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d56062 q = 1) (hb : d66088 q = 1) : d3928 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d56062, d3928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d56062, d3928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h16 p ha hb
theorem andIntro3327 (p : Pattern) (ha : d56068 p = 1) (hb : d66088 p = 1) : d3934 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56063 q = 1) (hb : d66088 q = 1) : d3929 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d56063, d3929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56063, d3929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3326 q ha hb
  have h2 (q : Pattern) (ha : d56064 q = 1) (hb : d66088 q = 1) : d3930 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d56064, d3930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56064, d3930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d56065 q = 1) (hb : d66088 q = 1) : d3931 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d56065, d3931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56065, d3931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d56066 q = 1) (hb : d66088 q = 1) : d3932 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d56066, d3932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56066, d3932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d56067 q = 1) (hb : d66088 q = 1) : d3933 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d56067, d3933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56067, d3933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d56068 q = 1) (hb : d66088 q = 1) : d3934 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d56068, d3934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56068, d3934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3328 (p : Pattern) (ha : d1629 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1626 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1627 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1627, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1628 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1629 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro3329 (p : Pattern) (ha : d1832 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1626 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1627 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1627, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1628 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1829 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1830 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1830, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d1831 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1832 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro3330 (p : Pattern) (ha : d1838 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1829 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1830 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1830, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1831 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1835 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1836 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1836, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1836, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d1837 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1838 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro3331 (p : Pattern) (ha : d2594 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1626 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1627 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1627, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1628 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2594 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h5 p ha hb
theorem andIntro3332 (p : Pattern) (ha : d51766 p = 1) (hb : d56773 p = 1) : d3940 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1649 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1650 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1650, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d1659 q = 1) : d1659 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d4526 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d51764 q = 1) (hb : d56773 q = 1) : d3938 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51764, d56773, d3938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d51764, d56773, d3938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d51765 q = 1) (hb : d56773 q = 1) : d3939 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51765, d3939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51765, d3939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51766 q = 1) (hb : d56773 q = 1) : d3940 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51766, d3940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51766, d3940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro3333 (p : Pattern) (ha : d51769 p = 1) (hb : d56773 p = 1) : d3943 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1649 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1650 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1650, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d1659 q = 1) : d1659 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d4526 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51764 q = 1) (hb : d56773 q = 1) : d3938 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51764, d56773, d3938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d51764, d56773, d3938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d51765 q = 1) (hb : d56773 q = 1) : d3939 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51765, d3939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51765, d3939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1807 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1808 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1808, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1808, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d1813 q = 1) : d1813 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d4531 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d51767 q = 1) (hb : d56773 q = 1) : d3941 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51767, d56773, d3941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d51767, d56773, d3941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d51768 q = 1) (hb : d56773 q = 1) : d3942 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51768, d3942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51768, d3942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d51769 q = 1) (hb : d56773 q = 1) : d3943 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51769, d3943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51769, d3943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro3334 (p : Pattern) (ha : d56074 p = 1) (hb : d66088 p = 1) : d3949 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1630 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3328 q ha hb
  have h2 (q : Pattern) (ha : d1631 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3071 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3071, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3071, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51770 q = 1) (hb : d56773 q = 1) : d3944 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51770, d3944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3332 q ha hb
    | true =>
      simp only [d51770, d3944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3333 q ha hb
  have h6 (q : Pattern) (ha : d1839 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3329 q ha hb
    | true =>
      simp only [d1839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3330 q ha hb
  have h7 (q : Pattern) (ha : d51771 q = 1) (hb : d56773 q = 1) : d3945 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51771, d3945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51771, d3945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51772 q = 1) (hb : d66088 q = 1) : d3946 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51772, d66088, d3946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51772, d66088, d3946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d56072 q = 1) (hb : d66088 q = 1) : d3947 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56072, d3947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d56072, d3947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2595 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3331 q ha hb
  have h11 (q : Pattern) (ha : d2596 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d2597 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2597, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2597, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d2598 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d56073 q = 1) (hb : d66088 q = 1) : d3948 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d56073, d3948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d56073, d3948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d56074 q = 1) (hb : d66088 q = 1) : d3949 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d56074, d3949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d56074, d3949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h16 p ha hb
theorem andIntro3335 (p : Pattern) (ha : d56080 p = 1) (hb : d66088 p = 1) : d3955 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56075 q = 1) (hb : d66088 q = 1) : d3950 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d56075, d3950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56075, d3950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3334 q ha hb
  have h2 (q : Pattern) (ha : d56076 q = 1) (hb : d66088 q = 1) : d3951 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d56076, d3951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56076, d3951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d56077 q = 1) (hb : d66088 q = 1) : d3952 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d56077, d3952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56077, d3952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d56078 q = 1) (hb : d66088 q = 1) : d3953 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d56078, d3953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56078, d3953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d56079 q = 1) (hb : d66088 q = 1) : d3954 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d56079, d3954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56079, d3954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d56080 q = 1) (hb : d66088 q = 1) : d3955 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d56080, d3955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56080, d3955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3336 (p : Pattern) (ha : d2112 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2109 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2110 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2110, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2111 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2112 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro3337 (p : Pattern) (ha : d2310 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2109 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2110 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2110, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2111 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d2307 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2308 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2308, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d2309 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2310 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro3338 (p : Pattern) (ha : d2316 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2307 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2308 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2308, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2309 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d2313 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2314 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2314, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2314, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d2315 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2316 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro3339 (p : Pattern) (ha : d2611 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2109 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2110 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2110, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2111 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2611 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h5 p ha hb
theorem andIntro3340 (p : Pattern) (ha : d51795 p = 1) (hb : d56773 p = 1) : d3962 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2132 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2133 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2133, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d2142 q = 1) : d2142 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d4567 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d51793 q = 1) (hb : d56773 q = 1) : d3960 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51793, d56773, d3960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d51793, d56773, d3960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d51794 q = 1) (hb : d56773 q = 1) : d3961 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51794, d3961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51794, d3961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51795 q = 1) (hb : d56773 q = 1) : d3962 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51795, d3962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51795, d3962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro3341 (p : Pattern) (ha : d51798 p = 1) (hb : d56773 p = 1) : d3965 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2132 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2133 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2133, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d2142 q = 1) : d2142 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d4567 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51793 q = 1) (hb : d56773 q = 1) : d3960 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51793, d56773, d3960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d51793, d56773, d3960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d51794 q = 1) (hb : d56773 q = 1) : d3961 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51794, d3961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51794, d3961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d2285 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2286 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2286, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2286, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d2291 q = 1) : d2291 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d4572 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d51796 q = 1) (hb : d56773 q = 1) : d3963 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51796, d56773, d3963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d51796, d56773, d3963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d51797 q = 1) (hb : d56773 q = 1) : d3964 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51797, d3964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51797, d3964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d51798 q = 1) (hb : d56773 q = 1) : d3965 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51798, d3965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51798, d3965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro3342 (p : Pattern) (ha : d56087 p = 1) (hb : d66088 p = 1) : d3971 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2113 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3336 q ha hb
  have h2 (q : Pattern) (ha : d2114 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3085 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3085, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3085, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51799 q = 1) (hb : d56773 q = 1) : d3966 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51799, d3966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3340 q ha hb
    | true =>
      simp only [d51799, d3966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3341 q ha hb
  have h6 (q : Pattern) (ha : d2317 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3337 q ha hb
    | true =>
      simp only [d2317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3338 q ha hb
  have h7 (q : Pattern) (ha : d51800 q = 1) (hb : d56773 q = 1) : d3967 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51800, d3967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51800, d3967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51801 q = 1) (hb : d66088 q = 1) : d3968 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51801, d66088, d3968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51801, d66088, d3968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d56085 q = 1) (hb : d66088 q = 1) : d3969 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56085, d3969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d56085, d3969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2612 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3339 q ha hb
  have h11 (q : Pattern) (ha : d2613 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d2614 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2614, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2614, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d2615 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d56086 q = 1) (hb : d66088 q = 1) : d3970 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d56086, d3970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d56086, d3970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d56087 q = 1) (hb : d66088 q = 1) : d3971 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d56087, d3971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d56087, d3971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h16 p ha hb
theorem andIntro3343 (p : Pattern) (ha : d56093 p = 1) (hb : d66088 p = 1) : d3977 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56088 q = 1) (hb : d66088 q = 1) : d3972 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d56088, d3972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56088, d3972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3342 q ha hb
  have h2 (q : Pattern) (ha : d56089 q = 1) (hb : d66088 q = 1) : d3973 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d56089, d3973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56089, d3973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d56090 q = 1) (hb : d66088 q = 1) : d3974 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d56090, d3974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56090, d3974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d56091 q = 1) (hb : d66088 q = 1) : d3975 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d56091, d3975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56091, d3975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d56092 q = 1) (hb : d66088 q = 1) : d3976 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d56092, d3976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56092, d3976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d56093 q = 1) (hb : d66088 q = 1) : d3977 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d56093, d3977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56093, d3977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3344 (p : Pattern) (ha : d56099 p = 1) (hb : d66088 p = 1) : d3983 p = 1 := by
  have h0 (q : Pattern) (ha : d56048 q = 1) (hb : d66088 q = 1) : d3896 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d56048, d3896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3303 q ha hb
    | true =>
      simp only [d56048, d3896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3311 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d56058 q = 1) (hb : d66088 q = 1) : d3915 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d56058, d3915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d56058, d3915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3319 q ha hb
  have h3 (q : Pattern) (ha : d56059 q = 1) (hb : d66088 q = 1) : d3916 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d56059, d3916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56059, d3916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d56069 q = 1) (hb : d66088 q = 1) : d3935 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d56069, d3935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d56069, d3935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3327 q ha hb
  have h5 (q : Pattern) (ha : d56070 q = 1) (hb : d66088 q = 1) : d3936 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d56070, d3936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d56070, d3936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d56071 q = 1) (hb : d66088 q = 1) : d3937 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d56071, d3937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d56071, d3937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d56081 q = 1) (hb : d66088 q = 1) : d3956 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d56081, d3956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d56081, d3956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3335 q ha hb
  have h8 (q : Pattern) (ha : d56082 q = 1) (hb : d66088 q = 1) : d3957 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d56082, d3957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d56082, d3957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d56083 q = 1) (hb : d66088 q = 1) : d3958 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d56083, d3958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d56083, d3958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d56084 q = 1) (hb : d66088 q = 1) : d3959 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d56084, d3959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d56084, d3959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d56094 q = 1) (hb : d66088 q = 1) : d3978 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d56094, d3978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d56094, d3978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3343 q ha hb
  have h12 (q : Pattern) (ha : d56095 q = 1) (hb : d66088 q = 1) : d3979 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d56095, d3979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d56095, d3979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d56096 q = 1) (hb : d66088 q = 1) : d3980 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d56096, d3980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d56096, d3980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d56097 q = 1) (hb : d66088 q = 1) : d3981 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d56097, d3981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d56097, d3981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d56098 q = 1) (hb : d66088 q = 1) : d3982 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d56098, d3982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d56098, d3982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d56099 q = 1) (hb : d66088 q = 1) : d3983 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d56099, d3983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d56099, d3983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro3345 (p : Pattern) (ha : d56105 p = 1) (hb : d66088 p = 1) : d3989 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56100 q = 1) (hb : d66088 q = 1) : d3984 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d56100, d3984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3344 q ha hb
    | true =>
      simp only [d56100, d3984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d56101 q = 1) (hb : d66088 q = 1) : d3985 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d56101, d3985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d56101, d3985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d56102 q = 1) (hb : d66088 q = 1) : d3986 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d56102, d3986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d56102, d3986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d56103 q = 1) (hb : d66088 q = 1) : d3987 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d56103, d3987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d56103, d3987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d56104 q = 1) (hb : d66088 q = 1) : d3988 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d56104, d3988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d56104, d3988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d56105 q = 1) (hb : d66088 q = 1) : d3989 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d56105, d3989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d56105, d3989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3346 (p : Pattern) (ha : d56111 p = 1) (hb : d66088 p = 1) : d3995 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56106 q = 1) (hb : d66088 q = 1) : d3990 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d56106, d3990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3345 q ha hb
    | true =>
      simp only [d56106, d3990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d56107 q = 1) (hb : d66088 q = 1) : d3991 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d56107, d3991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d56107, d3991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d56108 q = 1) (hb : d66088 q = 1) : d3992 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d56108, d3992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d56108, d3992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d56109 q = 1) (hb : d66088 q = 1) : d3993 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d56109, d3993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d56109, d3993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d56110 q = 1) (hb : d66088 q = 1) : d3994 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d56110, d3994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d56110, d3994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d56111 q = 1) (hb : d66088 q = 1) : d3995 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d56111, d3995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d56111, d3995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3347 (p : Pattern) (ha : d56117 p = 1) (hb : d66088 p = 1) : d4001 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56112 q = 1) (hb : d66088 q = 1) : d3996 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d56112, d3996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3346 q ha hb
    | true =>
      simp only [d56112, d3996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d56113 q = 1) (hb : d66088 q = 1) : d3997 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d56113, d3997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d56113, d3997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d56114 q = 1) (hb : d66088 q = 1) : d3998 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d56114, d3998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d56114, d3998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d56115 q = 1) (hb : d66088 q = 1) : d3999 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d56115, d3999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d56115, d3999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d56116 q = 1) (hb : d66088 q = 1) : d4000 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d56116, d4000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d56116, d4000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d56117 q = 1) (hb : d66088 q = 1) : d4001 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d56117, d4001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d56117, d4001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3348 (p : Pattern) (ha : d56123 p = 1) (hb : d66088 p = 1) : d4007 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56118 q = 1) (hb : d66088 q = 1) : d4002 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d56118, d4002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3347 q ha hb
    | true =>
      simp only [d56118, d4002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d56119 q = 1) (hb : d66088 q = 1) : d4003 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d56119, d4003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d56119, d4003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d56120 q = 1) (hb : d66088 q = 1) : d4004 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d56120, d4004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d56120, d4004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d56121 q = 1) (hb : d66088 q = 1) : d4005 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d56121, d4005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d56121, d4005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d56122 q = 1) (hb : d66088 q = 1) : d4006 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d56122, d4006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d56122, d4006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d56123 q = 1) (hb : d66088 q = 1) : d4007 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d56123, d4007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d56123, d4007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3349 (p : Pattern) (ha : d56129 p = 1) (hb : d66088 p = 1) : d4013 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56124 q = 1) (hb : d66088 q = 1) : d4008 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d56124, d4008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3348 q ha hb
    | true =>
      simp only [d56124, d4008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d56125 q = 1) (hb : d66088 q = 1) : d4009 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d56125, d4009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d56125, d4009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d56126 q = 1) (hb : d66088 q = 1) : d4010 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d56126, d4010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d56126, d4010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d56127 q = 1) (hb : d66088 q = 1) : d4011 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d56127, d4011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d56127, d4011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d56128 q = 1) (hb : d66088 q = 1) : d4012 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d56128, d4012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d56128, d4012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d56129 q = 1) (hb : d66088 q = 1) : d4013 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d56129, d4013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d56129, d4013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3350 (p : Pattern) (ha : d56135 p = 1) (hb : d66091 p = 1) : d4019 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56130 q = 1) (hb : d66088 q = 1) : d4014 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d56130, d4014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3349 q ha hb
    | true =>
      simp only [d56130, d4014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d56131 q = 1) (hb : d66088 q = 1) : d4015 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d56131, d4015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d56131, d4015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d56132 q = 1) (hb : d66088 q = 1) : d4016 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d56132, d4016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d56132, d4016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d66090 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d56133 q = 1) (hb : d66091 q = 1) : d4017 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d56133, d66091, d4017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d56133, d66091, d4017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d66091 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d56134 q = 1) (hb : d66091 q = 1) : d4018 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d56134, d4018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d56134, d4018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d56135 q = 1) (hb : d66091 q = 1) : d4019 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d56135, d4019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d56135, d4019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro3351 (p : Pattern) (ha : d56141 p = 1) (hb : d66091 p = 1) : d4025 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66091 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56136 q = 1) (hb : d66091 q = 1) : d4020 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d56136, d4020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3350 q ha hb
    | true =>
      simp only [d56136, d4020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d56137 q = 1) (hb : d66091 q = 1) : d4021 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d56137, d4021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d56137, d4021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d56138 q = 1) (hb : d66091 q = 1) : d4022 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d56138, d4022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d56138, d4022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d56139 q = 1) (hb : d66091 q = 1) : d4023 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d56139, d4023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d56139, d4023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d56140 q = 1) (hb : d66091 q = 1) : d4024 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d56140, d4024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d56140, d4024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d56141 q = 1) (hb : d66091 q = 1) : d4025 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d56141, d4025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d56141, d4025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3352 (p : Pattern) (ha : d3845 p = 1) (hb : d66094 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d124 q = 1) (hb : d51976 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
    | true =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125 q = 1) (hb : d51977 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d126 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3843 q = 1) (hb : d66092 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3843, d66092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3843, d66092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3844 q = 1) (hb : d66093 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3844, d66093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3844, d66093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3845 q = 1) (hb : d66094 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3845, d66094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3845, d66094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3353 (p : Pattern) (ha : d3848 p = 1) (hb : d66097 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d124 q = 1) (hb : d51976 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
    | true =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125 q = 1) (hb : d51977 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d126 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3843 q = 1) (hb : d66092 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3843, d66092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3843, d66092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3844 q = 1) (hb : d66093 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3844, d66093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3844, d66093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d200 q = 1) (hb : d52020 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, d52020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q ha hb
    | true =>
      simp only [d200, d52020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d201 q = 1) (hb : d52021 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, d52021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, d52021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202 q = 1) (hb : d52022 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, d52022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202, d52022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d3846 q = 1) (hb : d66095 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3846, d66095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d3846, d66095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d3847 q = 1) (hb : d66096 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3847, d66096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3847, d66096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d3848 q = 1) (hb : d66097 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3848, d66097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3848, d66097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro3354 (p : Pattern) (ha : d3854 p = 1) (hb : d66103 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3849 q = 1) (hb : d66098 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3849, d66098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3352 q ha hb
    | true =>
      simp only [d3849, d66098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3353 q ha hb
  have h2 (q : Pattern) (ha : d3850 q = 1) (hb : d66099 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3850, d66099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3850, d66099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3851 q = 1) (hb : d66100 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3851, d66100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3851, d66100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3852 q = 1) (hb : d66101 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3852, d66101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3852, d66101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3853 q = 1) (hb : d66102 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3853, d66102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3853, d66102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3854 q = 1) (hb : d66103 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3854, d66103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3854, d66103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3355 (p : Pattern) (ha : d3862 p = 1) (hb : d66111 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d304 q = 1) (hb : d52103 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d52103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52 q ha hb
    | true =>
      simp only [d304, d52103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
  have h2 (q : Pattern) (ha : d305 q = 1) (hb : d52104 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d52104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d52104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d306 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d52105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d306, d52105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3860 q = 1) (hb : d66109 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3860, d66109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3860, d66109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3861 q = 1) (hb : d66110 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3861, d66110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3861, d66110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3862 q = 1) (hb : d66111 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3862, d66111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3862, d66111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3356 (p : Pattern) (ha : d3865 p = 1) (hb : d66114 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d304 q = 1) (hb : d52103 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d52103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52 q ha hb
    | true =>
      simp only [d304, d52103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
  have h2 (q : Pattern) (ha : d305 q = 1) (hb : d52104 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d52104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d52104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d306 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d52105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d306, d52105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3860 q = 1) (hb : d66109 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3860, d66109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3860, d66109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3861 q = 1) (hb : d66110 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3861, d66110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3861, d66110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d382 q = 1) (hb : d52150 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d382, d52150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56 q ha hb
    | true =>
      simp only [d382, d52150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q ha hb
  have h7 (q : Pattern) (ha : d383 q = 1) (hb : d52151 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d383, d52151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d383, d52151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d384 q = 1) (hb : d52152 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d384, d52152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d384, d52152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d3863 q = 1) (hb : d66112 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3863, d66112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d3863, d66112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d3864 q = 1) (hb : d66113 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3864, d66113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3864, d66113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d3865 q = 1) (hb : d66114 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3865, d66114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3865, d66114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro3357 (p : Pattern) (ha : d3871 p = 1) (hb : d66120 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3866 q = 1) (hb : d66115 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3866, d66115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3355 q ha hb
    | true =>
      simp only [d3866, d66115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3356 q ha hb
  have h2 (q : Pattern) (ha : d3867 q = 1) (hb : d66116 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3867, d66116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3867, d66116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3868 q = 1) (hb : d66117 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3868, d66117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3868, d66117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3869 q = 1) (hb : d66118 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3869, d66118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3869, d66118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3870 q = 1) (hb : d66119 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3870, d66119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3870, d66119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3871 q = 1) (hb : d66120 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3871, d66120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3871, d66120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3358 (p : Pattern) (ha : d3877 p = 1) (hb : d66126 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3855 q = 1) (hb : d66104 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3855, d66104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3855, d66104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3354 q ha hb
  have h2 (q : Pattern) (ha : d3856 q = 1) (hb : d66105 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3856, d66105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3856, d66105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3857 q = 1) (hb : d66106 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3857, d66106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3857, d66106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3858 q = 1) (hb : d66107 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3858, d66107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3858, d66107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3859 q = 1) (hb : d66108 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3859, d66108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3859, d66108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3872 q = 1) (hb : d66121 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3872, d66121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3872, d66121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3357 q ha hb
  have h7 (q : Pattern) (ha : d3873 q = 1) (hb : d66122 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3873, d66122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3873, d66122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d3874 q = 1) (hb : d66123 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3874, d66123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3874, d66123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d3875 q = 1) (hb : d66124 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3875, d66124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3875, d66124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d3876 q = 1) (hb : d66125 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3876, d66125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3876, d66125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d3877 q = 1) (hb : d66126 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3877, d66126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3877, d66126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro3359 (p : Pattern) (ha : d3880 p = 1) (hb : d66129 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d525 q = 1) (hb : d52272 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d525, d52272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89 q ha hb
    | true =>
      simp only [d525, d52272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90 q ha hb
  have h2 (q : Pattern) (ha : d526 q = 1) (hb : d52273 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d526, d52273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d526, d52273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d527 q = 1) (hb : d52274 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d527, d52274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d527, d52274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3878 q = 1) (hb : d66127 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3878, d66127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3878, d66127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3879 q = 1) (hb : d66128 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3879, d66128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3879, d66128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3880 q = 1) (hb : d66129 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3880, d66129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3880, d66129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3360 (p : Pattern) (ha : d3883 p = 1) (hb : d66132 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d525 q = 1) (hb : d52272 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d525, d52272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89 q ha hb
    | true =>
      simp only [d525, d52272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90 q ha hb
  have h2 (q : Pattern) (ha : d526 q = 1) (hb : d52273 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d526, d52273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d526, d52273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d527 q = 1) (hb : d52274 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d527, d52274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d527, d52274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3878 q = 1) (hb : d66127 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3878, d66127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3878, d66127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3879 q = 1) (hb : d66128 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3879, d66128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3879, d66128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d617 q = 1) (hb : d52324 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d617, d52324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro95 q ha hb
    | true =>
      simp only [d617, d52324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96 q ha hb
  have h7 (q : Pattern) (ha : d618 q = 1) (hb : d52325 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d618, d52325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d618, d52325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d619 q = 1) (hb : d52326 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d619, d52326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d619, d52326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d3881 q = 1) (hb : d66130 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3881, d66130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d3881, d66130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d3882 q = 1) (hb : d66131 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3882, d66131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3882, d66131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d3883 q = 1) (hb : d66132 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3883, d66132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3883, d66132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro3361 (p : Pattern) (ha : d3889 p = 1) (hb : d66138 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3884 q = 1) (hb : d66133 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3884, d66133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3359 q ha hb
    | true =>
      simp only [d3884, d66133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3360 q ha hb
  have h2 (q : Pattern) (ha : d3885 q = 1) (hb : d66134 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3885, d66134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3885, d66134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3886 q = 1) (hb : d66135 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3886, d66135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3886, d66135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3887 q = 1) (hb : d66136 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3887, d66136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3887, d66136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3888 q = 1) (hb : d66137 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3888, d66137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3888, d66137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3889 q = 1) (hb : d66138 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3889, d66138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3889, d66138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3362 (p : Pattern) (ha : d3895 p = 1) (hb : d66144 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3890 q = 1) (hb : d66139 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3890, d66139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3890, d66139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3361 q ha hb
  have h2 (q : Pattern) (ha : d3891 q = 1) (hb : d66140 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3891, d66140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3891, d66140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3892 q = 1) (hb : d66141 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3892, d66141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3892, d66141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3893 q = 1) (hb : d66142 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3893, d66142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3893, d66142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3894 q = 1) (hb : d66143 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3894, d66143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3894, d66143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3895 q = 1) (hb : d66144 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3895, d66144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3895, d66144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3363 (p : Pattern) (ha : d3899 p = 1) (hb : d66148 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d817 q = 1) (hb : d52494 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d817, d52494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro136 q ha hb
    | true =>
      simp only [d817, d52494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro137 q ha hb
  have h2 (q : Pattern) (ha : d818 q = 1) (hb : d52495 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d818, d52495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d818, d52495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d819 q = 1) (hb : d52496 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, d52496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d819, d52496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3897 q = 1) (hb : d66146 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3897, d66146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3897, d66146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3898 q = 1) (hb : d66147 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3898, d66147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3898, d66147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3899 q = 1) (hb : d66148 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3899, d66148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3899, d66148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3364 (p : Pattern) (ha : d3902 p = 1) (hb : d66151 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d817 q = 1) (hb : d52494 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d817, d52494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro136 q ha hb
    | true =>
      simp only [d817, d52494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro137 q ha hb
  have h2 (q : Pattern) (ha : d818 q = 1) (hb : d52495 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d818, d52495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d818, d52495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d819 q = 1) (hb : d52496 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, d52496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d819, d52496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3897 q = 1) (hb : d66146 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3897, d66146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3897, d66146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3898 q = 1) (hb : d66147 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3898, d66147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3898, d66147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d923 q = 1) (hb : d52545 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d923, d52545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro142 q ha hb
    | true =>
      simp only [d923, d52545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro143 q ha hb
  have h7 (q : Pattern) (ha : d924 q = 1) (hb : d52546 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d924, d52546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d924, d52546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d925 q = 1) (hb : d52547 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d925, d52547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d925, d52547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d3900 q = 1) (hb : d66149 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3900, d66149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d3900, d66149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d3901 q = 1) (hb : d66150 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3901, d66150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3901, d66150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d3902 q = 1) (hb : d66151 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3902, d66151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3902, d66151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro3365 (p : Pattern) (ha : d3908 p = 1) (hb : d66157 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3903 q = 1) (hb : d66152 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3903, d66152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3363 q ha hb
    | true =>
      simp only [d3903, d66152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3364 q ha hb
  have h2 (q : Pattern) (ha : d3904 q = 1) (hb : d66153 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3904, d66153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3904, d66153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3905 q = 1) (hb : d66154 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3905, d66154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3905, d66154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3906 q = 1) (hb : d66155 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3906, d66155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3906, d66155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3907 q = 1) (hb : d66156 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3907, d66156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3907, d66156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3908 q = 1) (hb : d66157 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3908, d66157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3908, d66157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3366 (p : Pattern) (ha : d3914 p = 1) (hb : d66163 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3909 q = 1) (hb : d66158 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3909, d66158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3909, d66158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3365 q ha hb
  have h2 (q : Pattern) (ha : d3910 q = 1) (hb : d66159 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3910, d66159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3910, d66159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3911 q = 1) (hb : d66160 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3911, d66160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3911, d66160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3912 q = 1) (hb : d66161 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3912, d66161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3912, d66161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3913 q = 1) (hb : d66162 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3913, d66162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3913, d66162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3914 q = 1) (hb : d66163 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3914, d66163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3914, d66163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3367 (p : Pattern) (ha : d3919 p = 1) (hb : d66168 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1196 q = 1) (hb : d52777 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1196, d52777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro188 q ha hb
    | true =>
      simp only [d1196, d52777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro189 q ha hb
  have h2 (q : Pattern) (ha : d1197 q = 1) (hb : d52778 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, d52778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1197, d52778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1198 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, d52779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1198, d52779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3917 q = 1) (hb : d66166 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3917, d66166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3917, d66166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3918 q = 1) (hb : d66167 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3918, d66167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3918, d66167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3919 q = 1) (hb : d66168 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3919, d66168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3919, d66168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3368 (p : Pattern) (ha : d3922 p = 1) (hb : d66171 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1196 q = 1) (hb : d52777 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1196, d52777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro188 q ha hb
    | true =>
      simp only [d1196, d52777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro189 q ha hb
  have h2 (q : Pattern) (ha : d1197 q = 1) (hb : d52778 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, d52778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1197, d52778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1198 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, d52779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1198, d52779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3917 q = 1) (hb : d66166 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3917, d66166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3917, d66166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3918 q = 1) (hb : d66167 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3918, d66167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3918, d66167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1334 q = 1) (hb : d52825 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1334, d52825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro194 q ha hb
    | true =>
      simp only [d1334, d52825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro195 q ha hb
  have h7 (q : Pattern) (ha : d1335 q = 1) (hb : d52826 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1335, d52826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1335, d52826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1336 q = 1) (hb : d52827 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1336, d52827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1336, d52827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d3920 q = 1) (hb : d66169 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3920, d66169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d3920, d66169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d3921 q = 1) (hb : d66170 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3921, d66170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3921, d66170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d3922 q = 1) (hb : d66171 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3922, d66171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3922, d66171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro3369 (p : Pattern) (ha : d3928 p = 1) (hb : d66177 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3923 q = 1) (hb : d66172 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3923, d66172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3367 q ha hb
    | true =>
      simp only [d3923, d66172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3368 q ha hb
  have h2 (q : Pattern) (ha : d3924 q = 1) (hb : d66173 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3924, d66173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3924, d66173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3925 q = 1) (hb : d66174 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3925, d66174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3925, d66174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3926 q = 1) (hb : d66175 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3926, d66175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3926, d66175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3927 q = 1) (hb : d66176 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3927, d66176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3927, d66176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3928 q = 1) (hb : d66177 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3928, d66177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3928, d66177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3370 (p : Pattern) (ha : d3934 p = 1) (hb : d66183 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3929 q = 1) (hb : d66178 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3929, d66178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3929, d66178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3369 q ha hb
  have h2 (q : Pattern) (ha : d3930 q = 1) (hb : d66179 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3930, d66179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3930, d66179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3931 q = 1) (hb : d66180 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3931, d66180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3931, d66180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3932 q = 1) (hb : d66181 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3932, d66181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3932, d66181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3933 q = 1) (hb : d66182 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3933, d66182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3933, d66182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3934 q = 1) (hb : d66183 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3934, d66183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3934, d66183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3371 (p : Pattern) (ha : d3940 p = 1) (hb : d66189 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1657 q = 1) (hb : d53098 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1657, d53098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro244 q ha hb
    | true =>
      simp only [d1657, d53098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro245 q ha hb
  have h2 (q : Pattern) (ha : d1658 q = 1) (hb : d53099 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1658, d53099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1658, d53099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1659 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, d53100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1659, d53100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3938 q = 1) (hb : d66187 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3938, d66187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3938, d66187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3939 q = 1) (hb : d66188 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3939, d66188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3939, d66188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3940 q = 1) (hb : d66189 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3940, d66189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3940, d66189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3372 (p : Pattern) (ha : d3943 p = 1) (hb : d66192 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1657 q = 1) (hb : d53098 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1657, d53098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro244 q ha hb
    | true =>
      simp only [d1657, d53098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro245 q ha hb
  have h2 (q : Pattern) (ha : d1658 q = 1) (hb : d53099 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1658, d53099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1658, d53099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1659 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, d53100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1659, d53100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3938 q = 1) (hb : d66187 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3938, d66187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3938, d66187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3939 q = 1) (hb : d66188 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3939, d66188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3939, d66188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1811 q = 1) (hb : d53140 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1811, d53140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro250 q ha hb
    | true =>
      simp only [d1811, d53140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro251 q ha hb
  have h7 (q : Pattern) (ha : d1812 q = 1) (hb : d53141 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1812, d53141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1812, d53141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1813 q = 1) (hb : d53142 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1813, d53142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1813, d53142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d3941 q = 1) (hb : d66190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3941, d66190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d3941, d66190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d3942 q = 1) (hb : d66191 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3942, d66191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3942, d66191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d3943 q = 1) (hb : d66192 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3943, d66192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3943, d66192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro3373 (p : Pattern) (ha : d3949 p = 1) (hb : d66198 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3944 q = 1) (hb : d66193 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3944, d66193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3371 q ha hb
    | true =>
      simp only [d3944, d66193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3372 q ha hb
  have h2 (q : Pattern) (ha : d3945 q = 1) (hb : d66194 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3945, d66194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3945, d66194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3946 q = 1) (hb : d66195 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3946, d66195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3946, d66195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3947 q = 1) (hb : d66196 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3947, d66196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3947, d66196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3948 q = 1) (hb : d66197 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3948, d66197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3948, d66197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3949 q = 1) (hb : d66198 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3949, d66198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3949, d66198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3374 (p : Pattern) (ha : d3955 p = 1) (hb : d66204 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3950 q = 1) (hb : d66199 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3950, d66199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3950, d66199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3373 q ha hb
  have h2 (q : Pattern) (ha : d3951 q = 1) (hb : d66200 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3951, d66200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3951, d66200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3952 q = 1) (hb : d66201 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3952, d66201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3952, d66201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3953 q = 1) (hb : d66202 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3953, d66202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3953, d66202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3954 q = 1) (hb : d66203 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3954, d66203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3954, d66203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3955 q = 1) (hb : d66204 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3955, d66204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3955, d66204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3375 (p : Pattern) (ha : d3962 p = 1) (hb : d66211 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2140 q = 1) (hb : d53419 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2140, d53419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro303 q ha hb
    | true =>
      simp only [d2140, d53419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro304 q ha hb
  have h2 (q : Pattern) (ha : d2141 q = 1) (hb : d53420 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2141, d53420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2141, d53420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2142 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, d53421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2142, d53421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3960 q = 1) (hb : d66209 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3960, d66209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3960, d66209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3961 q = 1) (hb : d66210 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3961, d66210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3961, d66210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3962 q = 1) (hb : d66211 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3962, d66211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3962, d66211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3376 (p : Pattern) (ha : d3965 p = 1) (hb : d66214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2140 q = 1) (hb : d53419 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2140, d53419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro303 q ha hb
    | true =>
      simp only [d2140, d53419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro304 q ha hb
  have h2 (q : Pattern) (ha : d2141 q = 1) (hb : d53420 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2141, d53420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2141, d53420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2142 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, d53421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2142, d53421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3960 q = 1) (hb : d66209 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3960, d66209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3960, d66209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3961 q = 1) (hb : d66210 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3961, d66210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3961, d66210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2289 q = 1) (hb : d53457 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2289, d53457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro309 q ha hb
    | true =>
      simp only [d2289, d53457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro310 q ha hb
  have h7 (q : Pattern) (ha : d2290 q = 1) (hb : d53458 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2290, d53458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2290, d53458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2291 q = 1) (hb : d53459 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2291, d53459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2291, d53459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d3963 q = 1) (hb : d66212 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3963, d66212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d3963, d66212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d3964 q = 1) (hb : d66213 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3964, d66213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3964, d66213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d3965 q = 1) (hb : d66214 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3965, d66214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3965, d66214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro3377 (p : Pattern) (ha : d3971 p = 1) (hb : d66220 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3966 q = 1) (hb : d66215 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3966, d66215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3375 q ha hb
    | true =>
      simp only [d3966, d66215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3376 q ha hb
  have h2 (q : Pattern) (ha : d3967 q = 1) (hb : d66216 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3967, d66216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3967, d66216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3968 q = 1) (hb : d66217 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3968, d66217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3968, d66217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3969 q = 1) (hb : d66218 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3969, d66218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3969, d66218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3970 q = 1) (hb : d66219 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3970, d66219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3970, d66219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3971 q = 1) (hb : d66220 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3971, d66220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3971, d66220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3378 (p : Pattern) (ha : d3977 p = 1) (hb : d66226 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3972 q = 1) (hb : d66221 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3972, d66221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3972, d66221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3377 q ha hb
  have h2 (q : Pattern) (ha : d3973 q = 1) (hb : d66222 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3973, d66222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3973, d66222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3974 q = 1) (hb : d66223 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3974, d66223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3974, d66223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3975 q = 1) (hb : d66224 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3975, d66224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3975, d66224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3976 q = 1) (hb : d66225 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3976, d66225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3976, d66225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3977 q = 1) (hb : d66226 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3977, d66226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3977, d66226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3379 (p : Pattern) (ha : d3983 p = 1) (hb : d66232 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d3896 q = 1) (hb : d66145 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3896, d66145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3358 q ha hb
    | true =>
      simp only [d3896, d66145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3362 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3915 q = 1) (hb : d66164 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3915, d66164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3915, d66164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3366 q ha hb
  have h3 (q : Pattern) (ha : d3916 q = 1) (hb : d66165 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3916, d66165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3916, d66165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3935 q = 1) (hb : d66184 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3935, d66184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3935, d66184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3370 q ha hb
  have h5 (q : Pattern) (ha : d3936 q = 1) (hb : d66185 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3936, d66185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3936, d66185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3937 q = 1) (hb : d66186 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3937, d66186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3937, d66186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3956 q = 1) (hb : d66205 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3956, d66205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3956, d66205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3374 q ha hb
  have h8 (q : Pattern) (ha : d3957 q = 1) (hb : d66206 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3957, d66206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3957, d66206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d3958 q = 1) (hb : d66207 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3958, d66207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3958, d66207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d3959 q = 1) (hb : d66208 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d3959, d66208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d3959, d66208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d3978 q = 1) (hb : d66227 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3978, d66227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3978, d66227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3378 q ha hb
  have h12 (q : Pattern) (ha : d3979 q = 1) (hb : d66228 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3979, d66228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3979, d66228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d3980 q = 1) (hb : d66229 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3980, d66229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3980, d66229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d3981 q = 1) (hb : d66230 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d3981, d66230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3981, d66230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d3982 q = 1) (hb : d66231 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d3982, d66231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d3982, d66231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d3983 q = 1) (hb : d66232 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d3983, d66232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d3983, d66232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro3380 (p : Pattern) (ha : d3989 p = 1) (hb : d66238 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3984 q = 1) (hb : d66233 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d3984, d66233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3379 q ha hb
    | true =>
      simp only [d3984, d66233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3985 q = 1) (hb : d66234 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d3985, d66234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3985, d66234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3986 q = 1) (hb : d66235 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d3986, d66235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3986, d66235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3987 q = 1) (hb : d66236 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d3987, d66236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3987, d66236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3988 q = 1) (hb : d66237 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d3988, d66237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3988, d66237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3989 q = 1) (hb : d66238 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d3989, d66238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3989, d66238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3381 (p : Pattern) (ha : d3995 p = 1) (hb : d66244 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3990 q = 1) (hb : d66239 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d3990, d66239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3380 q ha hb
    | true =>
      simp only [d3990, d66239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3991 q = 1) (hb : d66240 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d3991, d66240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3991, d66240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3992 q = 1) (hb : d66241 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d3992, d66241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3992, d66241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3993 q = 1) (hb : d66242 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d3993, d66242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3993, d66242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3994 q = 1) (hb : d66243 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d3994, d66243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3994, d66243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3995 q = 1) (hb : d66244 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d3995, d66244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3995, d66244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3382 (p : Pattern) (ha : d4001 p = 1) (hb : d66250 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3996 q = 1) (hb : d66245 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d3996, d66245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3381 q ha hb
    | true =>
      simp only [d3996, d66245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3997 q = 1) (hb : d66246 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d3997, d66246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3997, d66246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3998 q = 1) (hb : d66247 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d3998, d66247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3998, d66247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3999 q = 1) (hb : d66248 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d3999, d66248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3999, d66248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4000 q = 1) (hb : d66249 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d4000, d66249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4000, d66249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4001 q = 1) (hb : d66250 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d4001, d66250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4001, d66250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3383 (p : Pattern) (ha : d4007 p = 1) (hb : d66256 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4002 q = 1) (hb : d66251 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d4002, d66251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3382 q ha hb
    | true =>
      simp only [d4002, d66251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4003 q = 1) (hb : d66252 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d4003, d66252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4003, d66252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4004 q = 1) (hb : d66253 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d4004, d66253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4004, d66253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4005 q = 1) (hb : d66254 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d4005, d66254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4005, d66254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4006 q = 1) (hb : d66255 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d4006, d66255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4006, d66255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4007 q = 1) (hb : d66256 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d4007, d66256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4007, d66256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3384 (p : Pattern) (ha : d4013 p = 1) (hb : d66262 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4008 q = 1) (hb : d66257 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d4008, d66257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3383 q ha hb
    | true =>
      simp only [d4008, d66257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4009 q = 1) (hb : d66258 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d4009, d66258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4009, d66258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4010 q = 1) (hb : d66259 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d4010, d66259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4010, d66259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4011 q = 1) (hb : d66260 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d4011, d66260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4011, d66260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4012 q = 1) (hb : d66261 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d4012, d66261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4012, d66261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4013 q = 1) (hb : d66262 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d4013, d66262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4013, d66262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3385 (p : Pattern) (ha : d4019 p = 1) (hb : d66268 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4014 q = 1) (hb : d66263 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d4014, d66263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3384 q ha hb
    | true =>
      simp only [d4014, d66263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4015 q = 1) (hb : d66264 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d4015, d66264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4015, d66264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4016 q = 1) (hb : d66265 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d4016, d66265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4016, d66265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4017 q = 1) (hb : d66266 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d4017, d66266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4017, d66266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4018 q = 1) (hb : d66267 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d4018, d66267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4018, d66267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4019 q = 1) (hb : d66268 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d4019, d66268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4019, d66268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3386 (p : Pattern) (ha : d4025 p = 1) (hb : d66274 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4020 q = 1) (hb : d66269 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d4020, d66269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3385 q ha hb
    | true =>
      simp only [d4020, d66269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4021 q = 1) (hb : d66270 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d4021, d66270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4021, d66270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4022 q = 1) (hb : d66271 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d4022, d66271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4022, d66271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4023 q = 1) (hb : d66272 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d4023, d66272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4023, d66272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4024 q = 1) (hb : d66273 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d4024, d66273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4024, d66273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4025 q = 1) (hb : d66274 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d4025, d66274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4025, d66274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3387 (p : Pattern) (ha : d54865 p = 1) (hb : d66088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3291 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3296 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53637 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53637, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53638 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54864 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d54865 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro3388 (p : Pattern) (ha : d291 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d281 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d282 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d282, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d283 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d288 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d289 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d290 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d291 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro3389 (p : Pattern) (ha : d54872 p = 1) (hb : d66088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3297 q ha hb
    | true =>
      simp only [d292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3388 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d293 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53653 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53653, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53653, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53654 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54871 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d54872 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro3390 (p : Pattern) (ha : d54878 p = 1) (hb : d66088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54866 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3387 q ha hb
  have h2 (q : Pattern) (ha : d54867 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54868 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54869 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54870 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54873 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3389 q ha hb
  have h7 (q : Pattern) (ha : d54874 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54875 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54876 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54877 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54878 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
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
theorem andIntro3391 (p : Pattern) (ha : d507 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d494 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d495 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d495, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d496 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d504 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d505 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d505, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d505, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d506 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d507 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro3392 (p : Pattern) (ha : d54880 p = 1) (hb : d66088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d508 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3304 q ha hb
    | true =>
      simp only [d508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3391 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d509 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53678 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53678, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53678, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53679 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54879 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d54880 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro3393 (p : Pattern) (ha : d54886 p = 1) (hb : d66088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54881 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3392 q ha hb
  have h2 (q : Pattern) (ha : d54882 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54883 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54884 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54885 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54886 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
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
theorem andIntro3394 (p : Pattern) (ha : d799 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d786 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d787 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d787, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d788 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d796 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d797 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d797, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d797, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d798 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d799 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro3395 (p : Pattern) (ha : d54889 p = 1) (hb : d66088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d800 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3312 q ha hb
    | true =>
      simp only [d800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3394 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d801 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53705 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53705, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53705, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53706 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54888 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d54889 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro3396 (p : Pattern) (ha : d54895 p = 1) (hb : d66088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54890 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3395 q ha hb
  have h2 (q : Pattern) (ha : d54891 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54892 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54893 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54894 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54895 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
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
theorem andIntro3397 (p : Pattern) (ha : d1178 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1165 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1166 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1166, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1167 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1175 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1176 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1176, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1176, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d1177 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1178 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro3398 (p : Pattern) (ha : d54899 p = 1) (hb : d66088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1179 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3320 q ha hb
    | true =>
      simp only [d1179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3397 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1180 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53733 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53733, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53733, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53734 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54898 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d54899 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro3399 (p : Pattern) (ha : d54905 p = 1) (hb : d66088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54900 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3398 q ha hb
  have h2 (q : Pattern) (ha : d54901 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54902 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54903 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54904 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54905 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
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
theorem andIntro3400 (p : Pattern) (ha : d1639 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1626 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1627 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1627, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1628 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1636 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1637 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1637, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1637, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d1638 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1639 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro3401 (p : Pattern) (ha : d54910 p = 1) (hb : d66088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1640 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3328 q ha hb
    | true =>
      simp only [d1640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3400 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1641 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53762 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53762, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53762, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53763 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54909 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d54910 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro3402 (p : Pattern) (ha : d54916 p = 1) (hb : d66088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54911 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3401 q ha hb
  have h2 (q : Pattern) (ha : d54912 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54913 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54914 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54915 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54916 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
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
theorem andIntro3403 (p : Pattern) (ha : d2122 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2109 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2110 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2110, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2111 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d2119 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2120 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2120, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2120, d56773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d2121 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2122 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro3404 (p : Pattern) (ha : d54922 p = 1) (hb : d66088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2123 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3336 q ha hb
    | true =>
      simp only [d2123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3403 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2124 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53792 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53792, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53792, d66088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53793 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54921 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d54922 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro3405 (p : Pattern) (ha : d54928 p = 1) (hb : d66088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54923 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3404 q ha hb
  have h2 (q : Pattern) (ha : d54924 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54925 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54926 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54927 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54928 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
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
theorem andIntro3406 (p : Pattern) (ha : d54934 p = 1) (hb : d66088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d54887 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3390 q ha hb
    | true =>
      simp only [d54887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3393 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54896 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3396 q ha hb
  have h3 (q : Pattern) (ha : d54897 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54906 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3399 q ha hb
  have h5 (q : Pattern) (ha : d54907 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54908 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54917 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3402 q ha hb
  have h8 (q : Pattern) (ha : d54918 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54919 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54920 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54929 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3405 q ha hb
  have h12 (q : Pattern) (ha : d54930 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54931 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54932 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54933 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54934 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
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
theorem andIntro3407 (p : Pattern) (ha : d54940 p = 1) (hb : d66088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54935 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3406 q ha hb
    | true =>
      simp only [d54935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54936 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54937 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54938 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54939 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54940 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
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
theorem andIntro3408 (p : Pattern) (ha : d54946 p = 1) (hb : d66088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54941 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3407 q ha hb
    | true =>
      simp only [d54941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54942 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54943 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54944 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54945 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54946 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
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
theorem andIntro3409 (p : Pattern) (ha : d54952 p = 1) (hb : d66088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54947 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3408 q ha hb
    | true =>
      simp only [d54947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54948 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54949 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54950 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54951 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54952 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
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
theorem andIntro3410 (p : Pattern) (ha : d54958 p = 1) (hb : d66088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54953 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3409 q ha hb
    | true =>
      simp only [d54953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54954 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54955 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54956 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54957 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54958 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
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
theorem andIntro3411 (p : Pattern) (ha : d54964 p = 1) (hb : d66088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54959 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3410 q ha hb
    | true =>
      simp only [d54959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54960 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54961 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54962 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54963 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54964 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
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
theorem andIntro3412 (p : Pattern) (ha : d54970 p = 1) (hb : d66091 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54965 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3411 q ha hb
    | true =>
      simp only [d54965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54966 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54967 q = 1) (hb : d66088 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d66090 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d54968 q = 1) (hb : d66091 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54968, d66091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54968, d66091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d66091 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d54969 q = 1) (hb : d66091 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54970 q = 1) (hb : d66091 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro3413 (p : Pattern) (ha : d54976 p = 1) (hb : d66091 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66091 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54971 q = 1) (hb : d66091 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3412 q ha hb
    | true =>
      simp only [d54971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54972 q = 1) (hb : d66091 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54973 q = 1) (hb : d66091 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54974 q = 1) (hb : d66091 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54975 q = 1) (hb : d66091 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54976 q = 1) (hb : d66091 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3414 (p : Pattern) (ha : d0 p = 1) (hb : d66274 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66274 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro3415 (p : Pattern) (ha : d0 p = 1) (hb : d4025 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d4025 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro3416 (p : Pattern) (ha : d2520 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3288 q ha hb
    | true =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3289 q ha hb
  have h2 (q : Pattern) (ha : d57 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d59 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2519 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2520 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3417 (p : Pattern) (ha : d54520 p = 1) (hb : d56773 p = 1) : d3854 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3291 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3291 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3296 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51647 q = 1) (hb : d56773 q = 1) : d3849 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51647, d3849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3293 q ha hb
    | true =>
      simp only [d51647, d3849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3294 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3292 q ha hb
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d51648 q = 1) (hb : d56773 q = 1) : d3850 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51648, d3850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51648, d3850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51649 q = 1) (hb : d56773 q = 1) : d3851 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51649, d3851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51649, d3851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51650 q = 1) (hb : d56773 q = 1) : d3852 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51650, d3852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51650, d3852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2525 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3292 q ha hb
  have h12 (q : Pattern) (ha : d2526 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d2527 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d2528 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d2528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d54519 q = 1) (hb : d56773 q = 1) : d3853 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54519, d3853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54519, d3853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54520 q = 1) (hb : d56773 q = 1) : d3854 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54520, d3854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54520, d3854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro3418 (p : Pattern) (ha : d54527 p = 1) (hb : d56773 p = 1) : d3871 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3297 q ha hb
  have h2 (q : Pattern) (ha : d286 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d292 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3297 q ha hb
    | true =>
      simp only [d292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3388 q ha hb
  have h4 (q : Pattern) (ha : d293 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d294 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51664 q = 1) (hb : d56773 q = 1) : d3866 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51664, d3866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3300 q ha hb
    | true =>
      simp only [d51664, d3866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3301 q ha hb
  have h7 (q : Pattern) (ha : d398 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3298 q ha hb
    | true =>
      simp only [d398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3296 q ha hb
  have h8 (q : Pattern) (ha : d51665 q = 1) (hb : d56773 q = 1) : d3867 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51665, d3867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51665, d3867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51666 q = 1) (hb : d56773 q = 1) : d3868 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51666, d3868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51666, d3868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51667 q = 1) (hb : d56773 q = 1) : d3869 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51667, d3869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51667, d3869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2537 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3299 q ha hb
  have h12 (q : Pattern) (ha : d2538 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d2539 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d2540 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d2540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d54526 q = 1) (hb : d56773 q = 1) : d3870 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54526, d3870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54526, d3870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54527 q = 1) (hb : d56773 q = 1) : d3871 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54527, d3871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54527, d3871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro3419 (p : Pattern) (ha : d54533 p = 1) (hb : d56773 p = 1) : d3877 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2521 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3416 q ha hb
  have h2 (q : Pattern) (ha : d2522 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2523 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2524 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54521 q = 1) (hb : d56773 q = 1) : d3855 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54521, d3855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54521, d3855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3417 q ha hb
  have h6 (q : Pattern) (ha : d54522 q = 1) (hb : d56773 q = 1) : d3856 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54522, d3856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54522, d3856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54523 q = 1) (hb : d56773 q = 1) : d3857 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54523, d3857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54523, d3857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54524 q = 1) (hb : d56773 q = 1) : d3858 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54524, d3858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54524, d3858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54525 q = 1) (hb : d56773 q = 1) : d3859 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54525, d3859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54525, d3859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54528 q = 1) (hb : d56773 q = 1) : d3872 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54528, d3872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54528, d3872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3418 q ha hb
  have h11 (q : Pattern) (ha : d54529 q = 1) (hb : d56773 q = 1) : d3873 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54529, d3873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54529, d3873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54530 q = 1) (hb : d56773 q = 1) : d3874 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54530, d3874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54530, d3874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54531 q = 1) (hb : d56773 q = 1) : d3875 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54531, d3875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54531, d3875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54532 q = 1) (hb : d56773 q = 1) : d3876 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54532, d3876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54532, d3876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54533 q = 1) (hb : d56773 q = 1) : d3877 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54533, d3877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d54533, d3877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro3420 (p : Pattern) (ha : d54535 p = 1) (hb : d56773 p = 1) : d3889 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d498 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3304 q ha hb
  have h2 (q : Pattern) (ha : d499 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d508 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3304 q ha hb
    | true =>
      simp only [d508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3391 q ha hb
  have h4 (q : Pattern) (ha : d509 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d510 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51689 q = 1) (hb : d56773 q = 1) : d3884 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51689, d3884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3308 q ha hb
    | true =>
      simp only [d51689, d3884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3309 q ha hb
  have h7 (q : Pattern) (ha : d645 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3305 q ha hb
    | true =>
      simp only [d645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3306 q ha hb
  have h8 (q : Pattern) (ha : d51690 q = 1) (hb : d56773 q = 1) : d3885 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51690, d3885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51690, d3885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51691 q = 1) (hb : d56773 q = 1) : d3886 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51691, d3886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51691, d3886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51692 q = 1) (hb : d56773 q = 1) : d3887 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51692, d3887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51692, d3887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2550 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3307 q ha hb
  have h12 (q : Pattern) (ha : d2551 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d2552 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d2553 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d2553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d54534 q = 1) (hb : d56773 q = 1) : d3888 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54534, d3888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54534, d3888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54535 q = 1) (hb : d56773 q = 1) : d3889 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54535, d3889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54535, d3889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro3421 (p : Pattern) (ha : d54541 p = 1) (hb : d56773 p = 1) : d3895 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54536 q = 1) (hb : d56773 q = 1) : d3890 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54536, d3890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54536, d3890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3420 q ha hb
  have h2 (q : Pattern) (ha : d54537 q = 1) (hb : d56773 q = 1) : d3891 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54537, d3891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54537, d3891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54538 q = 1) (hb : d56773 q = 1) : d3892 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54538, d3892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54538, d3892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54539 q = 1) (hb : d56773 q = 1) : d3893 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54539, d3893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54539, d3893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54540 q = 1) (hb : d56773 q = 1) : d3894 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54540, d3894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54540, d3894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54541 q = 1) (hb : d56773 q = 1) : d3895 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54541, d3895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54541, d3895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3422 (p : Pattern) (ha : d54544 p = 1) (hb : d56773 p = 1) : d3908 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d790 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3312 q ha hb
  have h2 (q : Pattern) (ha : d791 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d800 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3312 q ha hb
    | true =>
      simp only [d800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3394 q ha hb
  have h4 (q : Pattern) (ha : d801 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d802 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51715 q = 1) (hb : d56773 q = 1) : d3903 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51715, d3903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3316 q ha hb
    | true =>
      simp only [d51715, d3903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3317 q ha hb
  have h7 (q : Pattern) (ha : d951 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3313 q ha hb
    | true =>
      simp only [d951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3314 q ha hb
  have h8 (q : Pattern) (ha : d51716 q = 1) (hb : d56773 q = 1) : d3904 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51716, d3904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51716, d3904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51717 q = 1) (hb : d56773 q = 1) : d3905 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51717, d3905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51717, d3905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51718 q = 1) (hb : d56773 q = 1) : d3906 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51718, d3906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51718, d3906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2564 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3315 q ha hb
  have h12 (q : Pattern) (ha : d2565 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d2566 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d2567 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d2567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d54543 q = 1) (hb : d56773 q = 1) : d3907 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54543, d3907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54543, d3907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54544 q = 1) (hb : d56773 q = 1) : d3908 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54544, d3908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54544, d3908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro3423 (p : Pattern) (ha : d54550 p = 1) (hb : d56773 p = 1) : d3914 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54545 q = 1) (hb : d56773 q = 1) : d3909 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54545, d3909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54545, d3909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3422 q ha hb
  have h2 (q : Pattern) (ha : d54546 q = 1) (hb : d56773 q = 1) : d3910 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54546, d3910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54546, d3910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54547 q = 1) (hb : d56773 q = 1) : d3911 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54547, d3911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54547, d3911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54548 q = 1) (hb : d56773 q = 1) : d3912 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54548, d3912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54548, d3912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54549 q = 1) (hb : d56773 q = 1) : d3913 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54549, d3913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54549, d3913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54550 q = 1) (hb : d56773 q = 1) : d3914 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54550, d3914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54550, d3914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3424 (p : Pattern) (ha : d54554 p = 1) (hb : d56773 p = 1) : d3928 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1169 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3320 q ha hb
  have h2 (q : Pattern) (ha : d1170 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1179 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3320 q ha hb
    | true =>
      simp only [d1179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3397 q ha hb
  have h4 (q : Pattern) (ha : d1180 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1181 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51742 q = 1) (hb : d56773 q = 1) : d3923 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51742, d3923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3324 q ha hb
    | true =>
      simp only [d51742, d3923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3325 q ha hb
  have h7 (q : Pattern) (ha : d1362 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3321 q ha hb
    | true =>
      simp only [d1362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3322 q ha hb
  have h8 (q : Pattern) (ha : d51743 q = 1) (hb : d56773 q = 1) : d3924 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51743, d3924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51743, d3924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51744 q = 1) (hb : d56773 q = 1) : d3925 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51744, d3925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51744, d3925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51745 q = 1) (hb : d56773 q = 1) : d3926 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51745, d3926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51745, d3926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2579 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3323 q ha hb
  have h12 (q : Pattern) (ha : d2580 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d2581 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d2582 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d2582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d54553 q = 1) (hb : d56773 q = 1) : d3927 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54553, d3927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54553, d3927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54554 q = 1) (hb : d56773 q = 1) : d3928 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54554, d3928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54554, d3928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro3425 (p : Pattern) (ha : d54560 p = 1) (hb : d56773 p = 1) : d3934 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54555 q = 1) (hb : d56773 q = 1) : d3929 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54555, d3929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54555, d3929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3424 q ha hb
  have h2 (q : Pattern) (ha : d54556 q = 1) (hb : d56773 q = 1) : d3930 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54556, d3930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54556, d3930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54557 q = 1) (hb : d56773 q = 1) : d3931 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54557, d3931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54557, d3931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54558 q = 1) (hb : d56773 q = 1) : d3932 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54558, d3932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54558, d3932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54559 q = 1) (hb : d56773 q = 1) : d3933 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54559, d3933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54559, d3933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54560 q = 1) (hb : d56773 q = 1) : d3934 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54560, d3934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54560, d3934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3426 (p : Pattern) (ha : d54565 p = 1) (hb : d56773 p = 1) : d3949 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1630 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3328 q ha hb
  have h2 (q : Pattern) (ha : d1631 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1640 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3328 q ha hb
    | true =>
      simp only [d1640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3400 q ha hb
  have h4 (q : Pattern) (ha : d1641 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1642 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51770 q = 1) (hb : d56773 q = 1) : d3944 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51770, d3944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3332 q ha hb
    | true =>
      simp only [d51770, d3944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3333 q ha hb
  have h7 (q : Pattern) (ha : d1839 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3329 q ha hb
    | true =>
      simp only [d1839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3330 q ha hb
  have h8 (q : Pattern) (ha : d51771 q = 1) (hb : d56773 q = 1) : d3945 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51771, d3945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51771, d3945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51772 q = 1) (hb : d56773 q = 1) : d3946 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51772, d3946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51772, d3946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51773 q = 1) (hb : d56773 q = 1) : d3947 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51773, d3947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51773, d3947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2595 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3331 q ha hb
  have h12 (q : Pattern) (ha : d2596 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d2597 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d2598 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d2598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d54564 q = 1) (hb : d56773 q = 1) : d3948 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54564, d3948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54564, d3948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54565 q = 1) (hb : d56773 q = 1) : d3949 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54565, d3949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54565, d3949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro3427 (p : Pattern) (ha : d54571 p = 1) (hb : d56773 p = 1) : d3955 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54566 q = 1) (hb : d56773 q = 1) : d3950 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54566, d3950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54566, d3950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3426 q ha hb
  have h2 (q : Pattern) (ha : d54567 q = 1) (hb : d56773 q = 1) : d3951 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54567, d3951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54567, d3951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54568 q = 1) (hb : d56773 q = 1) : d3952 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54568, d3952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54568, d3952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54569 q = 1) (hb : d56773 q = 1) : d3953 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54569, d3953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54569, d3953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54570 q = 1) (hb : d56773 q = 1) : d3954 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54570, d3954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54570, d3954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54571 q = 1) (hb : d56773 q = 1) : d3955 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54571, d3955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54571, d3955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3428 (p : Pattern) (ha : d54577 p = 1) (hb : d56773 p = 1) : d3971 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2113 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3336 q ha hb
  have h2 (q : Pattern) (ha : d2114 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2123 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3336 q ha hb
    | true =>
      simp only [d2123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3403 q ha hb
  have h4 (q : Pattern) (ha : d2124 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2125 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51799 q = 1) (hb : d56773 q = 1) : d3966 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51799, d3966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3340 q ha hb
    | true =>
      simp only [d51799, d3966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3341 q ha hb
  have h7 (q : Pattern) (ha : d2317 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3337 q ha hb
    | true =>
      simp only [d2317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3338 q ha hb
  have h8 (q : Pattern) (ha : d51800 q = 1) (hb : d56773 q = 1) : d3967 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51800, d3967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51800, d3967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51801 q = 1) (hb : d56773 q = 1) : d3968 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51801, d3968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51801, d3968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51802 q = 1) (hb : d56773 q = 1) : d3969 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51802, d3969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51802, d3969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2612 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3339 q ha hb
  have h12 (q : Pattern) (ha : d2613 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d2614 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d2615 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d2615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d54576 q = 1) (hb : d56773 q = 1) : d3970 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54576, d3970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54576, d3970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54577 q = 1) (hb : d56773 q = 1) : d3971 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54577, d3971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54577, d3971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro3429 (p : Pattern) (ha : d54583 p = 1) (hb : d56773 p = 1) : d3977 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54578 q = 1) (hb : d56773 q = 1) : d3972 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54578, d3972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54578, d3972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3428 q ha hb
  have h2 (q : Pattern) (ha : d54579 q = 1) (hb : d56773 q = 1) : d3973 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54579, d3973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54579, d3973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54580 q = 1) (hb : d56773 q = 1) : d3974 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54580, d3974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54580, d3974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54581 q = 1) (hb : d56773 q = 1) : d3975 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54581, d3975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54581, d3975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54582 q = 1) (hb : d56773 q = 1) : d3976 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54582, d3976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54582, d3976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54583 q = 1) (hb : d56773 q = 1) : d3977 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54583, d3977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54583, d3977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3430 (p : Pattern) (ha : d54589 p = 1) (hb : d56773 p = 1) : d3983 p = 1 := by
  have h0 (q : Pattern) (ha : d54542 q = 1) (hb : d56773 q = 1) : d3896 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54542, d3896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3419 q ha hb
    | true =>
      simp only [d54542, d3896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3421 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54551 q = 1) (hb : d56773 q = 1) : d3915 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54551, d3915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54551, d3915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3423 q ha hb
  have h3 (q : Pattern) (ha : d54552 q = 1) (hb : d56773 q = 1) : d3916 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54552, d3916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54552, d3916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54561 q = 1) (hb : d56773 q = 1) : d3935 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54561, d3935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54561, d3935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3425 q ha hb
  have h5 (q : Pattern) (ha : d54562 q = 1) (hb : d56773 q = 1) : d3936 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54562, d3936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54562, d3936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54563 q = 1) (hb : d56773 q = 1) : d3937 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54563, d3937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54563, d3937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54572 q = 1) (hb : d56773 q = 1) : d3956 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54572, d3956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54572, d3956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3427 q ha hb
  have h8 (q : Pattern) (ha : d54573 q = 1) (hb : d56773 q = 1) : d3957 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54573, d3957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54573, d3957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54574 q = 1) (hb : d56773 q = 1) : d3958 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54574, d3958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54574, d3958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54575 q = 1) (hb : d56773 q = 1) : d3959 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54575, d3959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54575, d3959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54584 q = 1) (hb : d56773 q = 1) : d3978 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54584, d3978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54584, d3978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3429 q ha hb
  have h12 (q : Pattern) (ha : d54585 q = 1) (hb : d56773 q = 1) : d3979 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54585, d3979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54585, d3979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54586 q = 1) (hb : d56773 q = 1) : d3980 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54586, d3980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54586, d3980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54587 q = 1) (hb : d56773 q = 1) : d3981 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54587, d3981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54587, d3981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54588 q = 1) (hb : d56773 q = 1) : d3982 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54588, d3982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54588, d3982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54589 q = 1) (hb : d56773 q = 1) : d3983 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d54589, d3983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54589, d3983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro3431 (p : Pattern) (ha : d54595 p = 1) (hb : d56773 p = 1) : d3989 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54590 q = 1) (hb : d56773 q = 1) : d3984 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54590, d3984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3430 q ha hb
    | true =>
      simp only [d54590, d3984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54591 q = 1) (hb : d56773 q = 1) : d3985 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54591, d3985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54591, d3985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54592 q = 1) (hb : d56773 q = 1) : d3986 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54592, d3986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54592, d3986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54593 q = 1) (hb : d56773 q = 1) : d3987 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54593, d3987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54593, d3987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54594 q = 1) (hb : d56773 q = 1) : d3988 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54594, d3988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54594, d3988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54595 q = 1) (hb : d56773 q = 1) : d3989 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d54595, d3989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54595, d3989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3432 (p : Pattern) (ha : d54601 p = 1) (hb : d56773 p = 1) : d3995 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54596 q = 1) (hb : d56773 q = 1) : d3990 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54596, d3990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3431 q ha hb
    | true =>
      simp only [d54596, d3990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54597 q = 1) (hb : d56773 q = 1) : d3991 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54597, d3991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54597, d3991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54598 q = 1) (hb : d56773 q = 1) : d3992 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54598, d3992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54598, d3992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54599 q = 1) (hb : d56773 q = 1) : d3993 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54599, d3993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54599, d3993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54600 q = 1) (hb : d56773 q = 1) : d3994 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54600, d3994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54600, d3994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54601 q = 1) (hb : d56773 q = 1) : d3995 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d54601, d3995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54601, d3995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3433 (p : Pattern) (ha : d54607 p = 1) (hb : d56773 p = 1) : d4001 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54602 q = 1) (hb : d56773 q = 1) : d3996 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54602, d3996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3432 q ha hb
    | true =>
      simp only [d54602, d3996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54603 q = 1) (hb : d56773 q = 1) : d3997 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54603, d3997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54603, d3997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54604 q = 1) (hb : d56773 q = 1) : d3998 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54604, d3998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54604, d3998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54605 q = 1) (hb : d56773 q = 1) : d3999 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54605, d3999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54605, d3999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54606 q = 1) (hb : d56773 q = 1) : d4000 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54606, d4000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54606, d4000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54607 q = 1) (hb : d56773 q = 1) : d4001 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d54607, d4001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54607, d4001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3434 (p : Pattern) (ha : d54613 p = 1) (hb : d56773 p = 1) : d4007 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54608 q = 1) (hb : d56773 q = 1) : d4002 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54608, d4002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3433 q ha hb
    | true =>
      simp only [d54608, d4002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54609 q = 1) (hb : d56773 q = 1) : d4003 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54609, d4003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54609, d4003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54610 q = 1) (hb : d56773 q = 1) : d4004 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54610, d4004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54610, d4004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54611 q = 1) (hb : d56773 q = 1) : d4005 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54611, d4005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54611, d4005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54612 q = 1) (hb : d56773 q = 1) : d4006 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54612, d4006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54612, d4006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54613 q = 1) (hb : d56773 q = 1) : d4007 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d54613, d4007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54613, d4007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3435 (p : Pattern) (ha : d54619 p = 1) (hb : d56773 p = 1) : d4013 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54614 q = 1) (hb : d56773 q = 1) : d4008 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54614, d4008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3434 q ha hb
    | true =>
      simp only [d54614, d4008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54615 q = 1) (hb : d56773 q = 1) : d4009 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54615, d4009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54615, d4009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54616 q = 1) (hb : d56773 q = 1) : d4010 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54616, d4010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54616, d4010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54617 q = 1) (hb : d56773 q = 1) : d4011 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54617, d4011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54617, d4011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54618 q = 1) (hb : d56773 q = 1) : d4012 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54618, d4012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54618, d4012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54619 q = 1) (hb : d56773 q = 1) : d4013 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d54619, d4013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54619, d4013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3436 (p : Pattern) (ha : d54625 p = 1) (hb : d66275 p = 1) : d4019 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54620 q = 1) (hb : d56773 q = 1) : d4014 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54620, d4014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3435 q ha hb
    | true =>
      simp only [d54620, d4014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54621 q = 1) (hb : d56773 q = 1) : d4015 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54621, d4015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54621, d4015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54622 q = 1) (hb : d56773 q = 1) : d4016 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54622, d4016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54622, d4016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d54623 q = 1) (hb : d66275 q = 1) : d4017 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54623, d66275, d4017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54623, d66275, d4017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d66275 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d54624 q = 1) (hb : d66275 q = 1) : d4018 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54624, d4018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54624, d4018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54625 q = 1) (hb : d66275 q = 1) : d4019 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54625, d4019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54625, d4019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro3437 (p : Pattern) (ha : d54631 p = 1) (hb : d66275 p = 1) : d4025 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66275 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54626 q = 1) (hb : d66275 q = 1) : d4020 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54626, d4020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3436 q ha hb
    | true =>
      simp only [d54626, d4020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54627 q = 1) (hb : d66275 q = 1) : d4021 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54627, d4021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54627, d4021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54628 q = 1) (hb : d66275 q = 1) : d4022 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54628, d4022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54628, d4022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54629 q = 1) (hb : d66275 q = 1) : d4023 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54629, d4023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54629, d4023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54630 q = 1) (hb : d66275 q = 1) : d4024 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54630, d4024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54630, d4024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54631 q = 1) (hb : d66275 q = 1) : d4025 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54631, d4025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54631, d4025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3438 (p : Pattern) (ha : d54865 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3291 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3296 q ha hb
  have h2 (q : Pattern) (ha : d113 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53637 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53638 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54864 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54865 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3439 (p : Pattern) (ha : d54872 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3297 q ha hb
    | true =>
      simp only [d292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3388 q ha hb
  have h2 (q : Pattern) (ha : d293 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53653 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53654 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54871 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54872 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3440 (p : Pattern) (ha : d54878 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54866 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3438 q ha hb
  have h2 (q : Pattern) (ha : d54867 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54868 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54869 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54870 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54873 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3439 q ha hb
  have h7 (q : Pattern) (ha : d54874 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54875 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54876 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54877 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54878 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
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
theorem andIntro3441 (p : Pattern) (ha : d54880 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d508 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3304 q ha hb
    | true =>
      simp only [d508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3391 q ha hb
  have h2 (q : Pattern) (ha : d509 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53678 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53679 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54879 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54880 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3442 (p : Pattern) (ha : d54886 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54881 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3441 q ha hb
  have h2 (q : Pattern) (ha : d54882 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54883 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54884 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54885 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54886 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
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
theorem andIntro3443 (p : Pattern) (ha : d54889 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d800 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3312 q ha hb
    | true =>
      simp only [d800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3394 q ha hb
  have h2 (q : Pattern) (ha : d801 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53705 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53706 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54888 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54889 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3444 (p : Pattern) (ha : d54895 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54890 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3443 q ha hb
  have h2 (q : Pattern) (ha : d54891 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54892 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54893 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54894 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54895 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
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
theorem andIntro3445 (p : Pattern) (ha : d54899 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1179 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3320 q ha hb
    | true =>
      simp only [d1179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3397 q ha hb
  have h2 (q : Pattern) (ha : d1180 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53733 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53734 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54898 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54899 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3446 (p : Pattern) (ha : d54905 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54900 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3445 q ha hb
  have h2 (q : Pattern) (ha : d54901 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54902 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54903 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54904 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54905 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
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
theorem andIntro3447 (p : Pattern) (ha : d54910 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1640 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3328 q ha hb
    | true =>
      simp only [d1640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3400 q ha hb
  have h2 (q : Pattern) (ha : d1641 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53762 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53763 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54909 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54910 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3448 (p : Pattern) (ha : d54916 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54911 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3447 q ha hb
  have h2 (q : Pattern) (ha : d54912 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54913 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54914 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54915 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54916 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
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
theorem andIntro3449 (p : Pattern) (ha : d54922 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2123 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3336 q ha hb
    | true =>
      simp only [d2123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3403 q ha hb
  have h2 (q : Pattern) (ha : d2124 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53792 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53793 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54921 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54922 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3450 (p : Pattern) (ha : d54928 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54923 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3449 q ha hb
  have h2 (q : Pattern) (ha : d54924 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54925 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54926 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54927 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54928 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
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
theorem andIntro3451 (p : Pattern) (ha : d54934 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d54887 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3440 q ha hb
    | true =>
      simp only [d54887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3442 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54896 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3444 q ha hb
  have h3 (q : Pattern) (ha : d54897 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54906 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3446 q ha hb
  have h5 (q : Pattern) (ha : d54907 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54908 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54917 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3448 q ha hb
  have h8 (q : Pattern) (ha : d54918 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54919 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54920 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54929 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3450 q ha hb
  have h12 (q : Pattern) (ha : d54930 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54931 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54932 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54933 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54934 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
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
theorem andIntro3452 (p : Pattern) (ha : d54940 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54935 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3451 q ha hb
    | true =>
      simp only [d54935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54936 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54937 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54938 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54939 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54940 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
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
theorem andIntro3453 (p : Pattern) (ha : d54946 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54941 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3452 q ha hb
    | true =>
      simp only [d54941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54942 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54943 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54944 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54945 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54946 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
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
theorem andIntro3454 (p : Pattern) (ha : d54952 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54947 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3453 q ha hb
    | true =>
      simp only [d54947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54948 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54949 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54950 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54951 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54952 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
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
theorem andIntro3455 (p : Pattern) (ha : d54958 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54953 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3454 q ha hb
    | true =>
      simp only [d54953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54954 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54955 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54956 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54957 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54958 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
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
theorem andIntro3456 (p : Pattern) (ha : d54964 p = 1) (hb : d56773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54959 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3455 q ha hb
    | true =>
      simp only [d54959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54960 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54961 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54962 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54963 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54964 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
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
theorem andIntro3457 (p : Pattern) (ha : d54970 p = 1) (hb : d66275 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54965 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3456 q ha hb
    | true =>
      simp only [d54965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54966 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54967 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d54968 q = 1) (hb : d66275 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54968, d66275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54968, d66275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d66275 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d54969 q = 1) (hb : d66275 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54970 q = 1) (hb : d66275 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro3458 (p : Pattern) (ha : d54976 p = 1) (hb : d66275 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66275 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54971 q = 1) (hb : d66275 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3457 q ha hb
    | true =>
      simp only [d54971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54972 q = 1) (hb : d66275 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54973 q = 1) (hb : d66275 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54974 q = 1) (hb : d66275 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54975 q = 1) (hb : d66275 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54976 q = 1) (hb : d66275 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3459 (p : Pattern) (ha : d51643 p = 1) (hb : d66279 p = 1) : d66776 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66279 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d66279 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4336 q = 1) (hb : d66277 q = 1) : d4336 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d51641 q = 1) (hb : d66279 q = 1) : d4337 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d66279, d4337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d51641, d66279, d4337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51642 q = 1) (hb : d66279 q = 1) : d66775 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d66775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51642, d66775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51643 q = 1) (hb : d66279 q = 1) : d66776 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51643, d66776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51643, d66776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3460 (p : Pattern) (ha : d51646 p = 1) (hb : d66279 p = 1) : d66778 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d66279 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4336 q = 1) (hb : d66277 q = 1) : d4336 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51641 q = 1) (hb : d66279 q = 1) : d4337 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d66279, d4337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d51641, d66279, d4337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51642 q = 1) (hb : d66279 q = 1) : d66775 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d66775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51642, d66775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d198 q = 1) (hb : d66279 q = 1) : d198 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d202 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4341 q = 1) (hb : d66277 q = 1) : d4341 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d51644 q = 1) (hb : d66279 q = 1) : d4342 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51644, d66279, d4342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d51644, d66279, d4342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51645 q = 1) (hb : d66279 q = 1) : d66777 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51645, d66777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51645, d66777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d51646 q = 1) (hb : d66279 q = 1) : d66778 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51646, d66778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51646, d66778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro3461 (p : Pattern) (ha : d54520 p = 1) (hb : d66279 p = 1) : d66784 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d66279 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51647 q = 1) (hb : d66279 q = 1) : d66779 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51647, d66779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3459 q ha hb
    | true =>
      simp only [d51647, d66779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3460 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d66279 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51648 q = 1) (hb : d66279 q = 1) : d66780 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51648, d66780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51648, d66780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d66279 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51649 q = 1) (hb : d66279 q = 1) : d66781 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51649, d66781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51649, d66781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51650 q = 1) (hb : d66279 q = 1) : d66782 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51650, d66782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51650, d66782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2528 q = 1) (hb : d66279 q = 1) : d2528 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54519 q = 1) (hb : d66279 q = 1) : d66783 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54519, d66783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54519, d66783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54520 q = 1) (hb : d66279 q = 1) : d66784 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54520, d66784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54520, d66784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro3462 (p : Pattern) (ha : d51660 p = 1) (hb : d66279 p = 1) : d66791 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66279 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d300 q = 1) (hb : d66279 q = 1) : d300 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4372 q = 1) (hb : d66277 q = 1) : d4372 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d51658 q = 1) (hb : d66279 q = 1) : d4373 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51658, d66279, d4373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d51658, d66279, d4373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51659 q = 1) (hb : d66279 q = 1) : d66790 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51659, d66790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51659, d66790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51660 q = 1) (hb : d66279 q = 1) : d66791 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51660, d66791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51660, d66791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3463 (p : Pattern) (ha : d51663 p = 1) (hb : d66279 p = 1) : d66793 p = 1 := by
  have h0 (q : Pattern) (ha : d300 q = 1) (hb : d66279 q = 1) : d300 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4372 q = 1) (hb : d66277 q = 1) : d4372 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51658 q = 1) (hb : d66279 q = 1) : d4373 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51658, d66279, d4373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d51658, d66279, d4373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51659 q = 1) (hb : d66279 q = 1) : d66790 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51659, d66790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51659, d66790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d380 q = 1) (hb : d66279 q = 1) : d380 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d384 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4377 q = 1) (hb : d66277 q = 1) : d4377 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d51661 q = 1) (hb : d66279 q = 1) : d4378 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51661, d66279, d4378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d51661, d66279, d4378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51662 q = 1) (hb : d66279 q = 1) : d66792 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51662, d66792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51662, d66792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d51663 q = 1) (hb : d66279 q = 1) : d66793 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51663, d66793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51663, d66793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro3464 (p : Pattern) (ha : d54527 p = 1) (hb : d66279 p = 1) : d66799 p = 1 := by
  have h0 (q : Pattern) (ha : d294 q = 1) (hb : d66279 q = 1) : d294 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51664 q = 1) (hb : d66279 q = 1) : d66794 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51664, d66794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3462 q ha hb
    | true =>
      simp only [d51664, d66794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3463 q ha hb
  have h2 (q : Pattern) (ha : d398 q = 1) (hb : d66279 q = 1) : d398 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51665 q = 1) (hb : d66279 q = 1) : d66795 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51665, d66795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51665, d66795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d66279 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51666 q = 1) (hb : d66279 q = 1) : d66796 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51666, d66796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51666, d66796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51667 q = 1) (hb : d66279 q = 1) : d66797 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51667, d66797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51667, d66797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2540 q = 1) (hb : d66279 q = 1) : d2540 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54526 q = 1) (hb : d66279 q = 1) : d66798 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54526, d66798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54526, d66798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54527 q = 1) (hb : d66279 q = 1) : d66799 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54527, d66799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54527, d66799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro3465 (p : Pattern) (ha : d54533 p = 1) (hb : d66279 p = 1) : d66805 p = 1 := by
  have h0 (q : Pattern) (ha : d2524 q = 1) (hb : d66279 q = 1) : d2524 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d66279 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54521 q = 1) (hb : d66279 q = 1) : d66785 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54521, d66785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54521, d66785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3461 q ha hb
  have h3 (q : Pattern) (ha : d54522 q = 1) (hb : d66279 q = 1) : d66786 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54522, d66786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54522, d66786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54523 q = 1) (hb : d66279 q = 1) : d66787 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54523, d66787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54523, d66787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54524 q = 1) (hb : d66279 q = 1) : d66788 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54524, d66788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54524, d66788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54525 q = 1) (hb : d66279 q = 1) : d66789 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54525, d66789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54525, d66789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54528 q = 1) (hb : d66279 q = 1) : d66800 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54528, d66800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54528, d66800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3464 q ha hb
  have h8 (q : Pattern) (ha : d54529 q = 1) (hb : d66279 q = 1) : d66801 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54529, d66801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54529, d66801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54530 q = 1) (hb : d66279 q = 1) : d66802 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54530, d66802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54530, d66802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54531 q = 1) (hb : d66279 q = 1) : d66803 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54531, d66803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54531, d66803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54532 q = 1) (hb : d66279 q = 1) : d66804 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54532, d66804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54532, d66804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54533 q = 1) (hb : d66279 q = 1) : d66805 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54533, d66805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54533, d66805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro3466 (p : Pattern) (ha : d51685 p = 1) (hb : d66279 p = 1) : d66807 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66279 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d518 q = 1) (hb : d66279 q = 1) : d518 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d527 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4409 q = 1) (hb : d66277 q = 1) : d4409 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d51683 q = 1) (hb : d66279 q = 1) : d4410 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51683, d66279, d4410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d51683, d66279, d4410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51684 q = 1) (hb : d66279 q = 1) : d66806 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51684, d66806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51684, d66806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51685 q = 1) (hb : d66279 q = 1) : d66807 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51685, d66807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51685, d66807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3467 (p : Pattern) (ha : d51688 p = 1) (hb : d66279 p = 1) : d66809 p = 1 := by
  have h0 (q : Pattern) (ha : d518 q = 1) (hb : d66279 q = 1) : d518 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d527 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4409 q = 1) (hb : d66277 q = 1) : d4409 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51683 q = 1) (hb : d66279 q = 1) : d4410 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51683, d66279, d4410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d51683, d66279, d4410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51684 q = 1) (hb : d66279 q = 1) : d66806 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51684, d66806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51684, d66806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d614 q = 1) (hb : d66279 q = 1) : d614 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d619 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4414 q = 1) (hb : d66277 q = 1) : d4414 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d51686 q = 1) (hb : d66279 q = 1) : d4415 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51686, d66279, d4415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d51686, d66279, d4415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51687 q = 1) (hb : d66279 q = 1) : d66808 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51687, d66808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51687, d66808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d51688 q = 1) (hb : d66279 q = 1) : d66809 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51688, d66809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51688, d66809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro3468 (p : Pattern) (ha : d54535 p = 1) (hb : d66279 p = 1) : d66815 p = 1 := by
  have h0 (q : Pattern) (ha : d510 q = 1) (hb : d66279 q = 1) : d510 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51689 q = 1) (hb : d66279 q = 1) : d66810 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51689, d66810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3466 q ha hb
    | true =>
      simp only [d51689, d66810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3467 q ha hb
  have h2 (q : Pattern) (ha : d645 q = 1) (hb : d66279 q = 1) : d645 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51690 q = 1) (hb : d66279 q = 1) : d66811 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51690, d66811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51690, d66811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d66279 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51691 q = 1) (hb : d66279 q = 1) : d66812 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51691, d66812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51691, d66812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51692 q = 1) (hb : d66279 q = 1) : d66813 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51692, d66813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51692, d66813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2553 q = 1) (hb : d66279 q = 1) : d2553 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54534 q = 1) (hb : d66279 q = 1) : d66814 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54534, d66814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54534, d66814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54535 q = 1) (hb : d66279 q = 1) : d66815 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54535, d66815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54535, d66815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro3469 (p : Pattern) (ha : d54541 p = 1) (hb : d66279 p = 1) : d66821 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66279 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54536 q = 1) (hb : d66279 q = 1) : d66816 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54536, d66816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54536, d66816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3468 q ha hb
  have h2 (q : Pattern) (ha : d54537 q = 1) (hb : d66279 q = 1) : d66817 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54537, d66817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54537, d66817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54538 q = 1) (hb : d66279 q = 1) : d66818 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54538, d66818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54538, d66818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54539 q = 1) (hb : d66279 q = 1) : d66819 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54539, d66819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54539, d66819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54540 q = 1) (hb : d66279 q = 1) : d66820 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54540, d66820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54540, d66820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54541 q = 1) (hb : d66279 q = 1) : d66821 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54541, d66821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54541, d66821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3470 (p : Pattern) (ha : d51711 p = 1) (hb : d66279 p = 1) : d66824 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66279 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d810 q = 1) (hb : d66279 q = 1) : d810 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d819 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4447 q = 1) (hb : d66277 q = 1) : d4447 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d51709 q = 1) (hb : d66279 q = 1) : d4448 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51709, d66279, d4448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d51709, d66279, d4448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51710 q = 1) (hb : d66279 q = 1) : d66823 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51710, d66823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51710, d66823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51711 q = 1) (hb : d66279 q = 1) : d66824 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51711, d66824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51711, d66824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3471 (p : Pattern) (ha : d51714 p = 1) (hb : d66279 p = 1) : d66826 p = 1 := by
  have h0 (q : Pattern) (ha : d810 q = 1) (hb : d66279 q = 1) : d810 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d819 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4447 q = 1) (hb : d66277 q = 1) : d4447 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51709 q = 1) (hb : d66279 q = 1) : d4448 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51709, d66279, d4448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d51709, d66279, d4448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51710 q = 1) (hb : d66279 q = 1) : d66823 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51710, d66823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51710, d66823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d920 q = 1) (hb : d66279 q = 1) : d920 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d925 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4452 q = 1) (hb : d66277 q = 1) : d4452 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d51712 q = 1) (hb : d66279 q = 1) : d4453 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51712, d66279, d4453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d51712, d66279, d4453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51713 q = 1) (hb : d66279 q = 1) : d66825 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51713, d66825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51713, d66825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d51714 q = 1) (hb : d66279 q = 1) : d66826 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51714, d66826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51714, d66826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro3472 (p : Pattern) (ha : d54544 p = 1) (hb : d66279 p = 1) : d66832 p = 1 := by
  have h0 (q : Pattern) (ha : d802 q = 1) (hb : d66279 q = 1) : d802 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51715 q = 1) (hb : d66279 q = 1) : d66827 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51715, d66827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3470 q ha hb
    | true =>
      simp only [d51715, d66827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3471 q ha hb
  have h2 (q : Pattern) (ha : d951 q = 1) (hb : d66279 q = 1) : d951 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51716 q = 1) (hb : d66279 q = 1) : d66828 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51716, d66828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51716, d66828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d66279 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51717 q = 1) (hb : d66279 q = 1) : d66829 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51717, d66829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51717, d66829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51718 q = 1) (hb : d66279 q = 1) : d66830 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51718, d66830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51718, d66830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2567 q = 1) (hb : d66279 q = 1) : d2567 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54543 q = 1) (hb : d66279 q = 1) : d66831 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54543, d66831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54543, d66831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54544 q = 1) (hb : d66279 q = 1) : d66832 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54544, d66832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54544, d66832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro3473 (p : Pattern) (ha : d54550 p = 1) (hb : d66279 p = 1) : d66838 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66279 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54545 q = 1) (hb : d66279 q = 1) : d66833 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54545, d66833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54545, d66833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3472 q ha hb
  have h2 (q : Pattern) (ha : d54546 q = 1) (hb : d66279 q = 1) : d66834 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54546, d66834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54546, d66834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54547 q = 1) (hb : d66279 q = 1) : d66835 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54547, d66835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54547, d66835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54548 q = 1) (hb : d66279 q = 1) : d66836 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54548, d66836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54548, d66836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54549 q = 1) (hb : d66279 q = 1) : d66837 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54549, d66837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54549, d66837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54550 q = 1) (hb : d66279 q = 1) : d66838 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54550, d66838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54550, d66838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3474 (p : Pattern) (ha : d51738 p = 1) (hb : d66279 p = 1) : d66842 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66279 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1189 q = 1) (hb : d66279 q = 1) : d1189 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1198 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4486 q = 1) (hb : d66277 q = 1) : d4486 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d51736 q = 1) (hb : d66279 q = 1) : d4487 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51736, d66279, d4487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d51736, d66279, d4487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51737 q = 1) (hb : d66279 q = 1) : d66841 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51737, d66841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51737, d66841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51738 q = 1) (hb : d66279 q = 1) : d66842 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51738, d66842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51738, d66842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3475 (p : Pattern) (ha : d51741 p = 1) (hb : d66279 p = 1) : d66844 p = 1 := by
  have h0 (q : Pattern) (ha : d1189 q = 1) (hb : d66279 q = 1) : d1189 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1198 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4486 q = 1) (hb : d66277 q = 1) : d4486 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51736 q = 1) (hb : d66279 q = 1) : d4487 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51736, d66279, d4487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d51736, d66279, d4487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51737 q = 1) (hb : d66279 q = 1) : d66841 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51737, d66841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51737, d66841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1331 q = 1) (hb : d66279 q = 1) : d1331 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1336 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4491 q = 1) (hb : d66277 q = 1) : d4491 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d51739 q = 1) (hb : d66279 q = 1) : d4492 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51739, d66279, d4492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d51739, d66279, d4492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51740 q = 1) (hb : d66279 q = 1) : d66843 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51740, d66843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51740, d66843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d51741 q = 1) (hb : d66279 q = 1) : d66844 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51741, d66844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51741, d66844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro3476 (p : Pattern) (ha : d54554 p = 1) (hb : d66279 p = 1) : d66850 p = 1 := by
  have h0 (q : Pattern) (ha : d1181 q = 1) (hb : d66279 q = 1) : d1181 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51742 q = 1) (hb : d66279 q = 1) : d66845 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51742, d66845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3474 q ha hb
    | true =>
      simp only [d51742, d66845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3475 q ha hb
  have h2 (q : Pattern) (ha : d1362 q = 1) (hb : d66279 q = 1) : d1362 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51743 q = 1) (hb : d66279 q = 1) : d66846 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51743, d66846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51743, d66846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d66279 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51744 q = 1) (hb : d66279 q = 1) : d66847 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51744, d66847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51744, d66847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51745 q = 1) (hb : d66279 q = 1) : d66848 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51745, d66848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51745, d66848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2582 q = 1) (hb : d66279 q = 1) : d2582 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54553 q = 1) (hb : d66279 q = 1) : d66849 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54553, d66849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54553, d66849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54554 q = 1) (hb : d66279 q = 1) : d66850 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54554, d66850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54554, d66850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro3477 (p : Pattern) (ha : d54560 p = 1) (hb : d66279 p = 1) : d66856 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66279 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54555 q = 1) (hb : d66279 q = 1) : d66851 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54555, d66851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54555, d66851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3476 q ha hb
  have h2 (q : Pattern) (ha : d54556 q = 1) (hb : d66279 q = 1) : d66852 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54556, d66852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54556, d66852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54557 q = 1) (hb : d66279 q = 1) : d66853 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54557, d66853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54557, d66853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54558 q = 1) (hb : d66279 q = 1) : d66854 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54558, d66854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54558, d66854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54559 q = 1) (hb : d66279 q = 1) : d66855 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54559, d66855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54559, d66855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54560 q = 1) (hb : d66279 q = 1) : d66856 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54560, d66856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54560, d66856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3478 (p : Pattern) (ha : d51766 p = 1) (hb : d66279 p = 1) : d66861 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66279 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1650 q = 1) (hb : d66279 q = 1) : d1650 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1659 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4526 q = 1) (hb : d66277 q = 1) : d4526 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d51764 q = 1) (hb : d66279 q = 1) : d4527 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51764, d66279, d4527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d51764, d66279, d4527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51765 q = 1) (hb : d66279 q = 1) : d66860 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51765, d66860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51765, d66860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51766 q = 1) (hb : d66279 q = 1) : d66861 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51766, d66861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51766, d66861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3479 (p : Pattern) (ha : d51769 p = 1) (hb : d66279 p = 1) : d66863 p = 1 := by
  have h0 (q : Pattern) (ha : d1650 q = 1) (hb : d66279 q = 1) : d1650 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1659 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4526 q = 1) (hb : d66277 q = 1) : d4526 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51764 q = 1) (hb : d66279 q = 1) : d4527 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51764, d66279, d4527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d51764, d66279, d4527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51765 q = 1) (hb : d66279 q = 1) : d66860 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51765, d66860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51765, d66860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1808 q = 1) (hb : d66279 q = 1) : d1808 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1813 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4531 q = 1) (hb : d66277 q = 1) : d4531 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d51767 q = 1) (hb : d66279 q = 1) : d4532 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51767, d66279, d4532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d51767, d66279, d4532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51768 q = 1) (hb : d66279 q = 1) : d66862 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51768, d66862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51768, d66862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d51769 q = 1) (hb : d66279 q = 1) : d66863 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51769, d66863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51769, d66863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro3480 (p : Pattern) (ha : d54565 p = 1) (hb : d66279 p = 1) : d66869 p = 1 := by
  have h0 (q : Pattern) (ha : d1642 q = 1) (hb : d66279 q = 1) : d1642 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51770 q = 1) (hb : d66279 q = 1) : d66864 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51770, d66864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3478 q ha hb
    | true =>
      simp only [d51770, d66864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3479 q ha hb
  have h2 (q : Pattern) (ha : d1839 q = 1) (hb : d66279 q = 1) : d1839 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51771 q = 1) (hb : d66279 q = 1) : d66865 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51771, d66865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51771, d66865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d66279 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51772 q = 1) (hb : d66279 q = 1) : d66866 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51772, d66866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51772, d66866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51773 q = 1) (hb : d66279 q = 1) : d66867 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51773, d66867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51773, d66867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2598 q = 1) (hb : d66279 q = 1) : d2598 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54564 q = 1) (hb : d66279 q = 1) : d66868 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54564, d66868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54564, d66868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54565 q = 1) (hb : d66279 q = 1) : d66869 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54565, d66869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54565, d66869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro3481 (p : Pattern) (ha : d54571 p = 1) (hb : d66279 p = 1) : d66875 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66279 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54566 q = 1) (hb : d66279 q = 1) : d66870 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54566, d66870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54566, d66870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3480 q ha hb
  have h2 (q : Pattern) (ha : d54567 q = 1) (hb : d66279 q = 1) : d66871 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54567, d66871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54567, d66871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54568 q = 1) (hb : d66279 q = 1) : d66872 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54568, d66872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54568, d66872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54569 q = 1) (hb : d66279 q = 1) : d66873 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54569, d66873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54569, d66873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54570 q = 1) (hb : d66279 q = 1) : d66874 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54570, d66874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54570, d66874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54571 q = 1) (hb : d66279 q = 1) : d66875 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54571, d66875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54571, d66875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3482 (p : Pattern) (ha : d51795 p = 1) (hb : d66279 p = 1) : d66881 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66279 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2133 q = 1) (hb : d66279 q = 1) : d2133 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2142 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4567 q = 1) (hb : d66277 q = 1) : d4567 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d51793 q = 1) (hb : d66279 q = 1) : d4568 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51793, d66279, d4568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d51793, d66279, d4568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51794 q = 1) (hb : d66279 q = 1) : d66880 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51794, d66880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51794, d66880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51795 q = 1) (hb : d66279 q = 1) : d66881 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51795, d66881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51795, d66881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3483 (p : Pattern) (ha : d51798 p = 1) (hb : d66279 p = 1) : d66883 p = 1 := by
  have h0 (q : Pattern) (ha : d2133 q = 1) (hb : d66279 q = 1) : d2133 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2142 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4567 q = 1) (hb : d66277 q = 1) : d4567 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51793 q = 1) (hb : d66279 q = 1) : d4568 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51793, d66279, d4568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d51793, d66279, d4568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51794 q = 1) (hb : d66279 q = 1) : d66880 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51794, d66880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51794, d66880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2286 q = 1) (hb : d66279 q = 1) : d2286 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d2291 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4572 q = 1) (hb : d66277 q = 1) : d4572 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d51796 q = 1) (hb : d66279 q = 1) : d4573 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51796, d66279, d4573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d51796, d66279, d4573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51797 q = 1) (hb : d66279 q = 1) : d66882 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51797, d66882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51797, d66882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d51798 q = 1) (hb : d66279 q = 1) : d66883 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51798, d66883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51798, d66883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro3484 (p : Pattern) (ha : d54577 p = 1) (hb : d66279 p = 1) : d66889 p = 1 := by
  have h0 (q : Pattern) (ha : d2125 q = 1) (hb : d66279 q = 1) : d2125 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51799 q = 1) (hb : d66279 q = 1) : d66884 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51799, d66884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3482 q ha hb
    | true =>
      simp only [d51799, d66884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3483 q ha hb
  have h2 (q : Pattern) (ha : d2317 q = 1) (hb : d66279 q = 1) : d2317 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51800 q = 1) (hb : d66279 q = 1) : d66885 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51800, d66885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51800, d66885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d66279 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51801 q = 1) (hb : d66279 q = 1) : d66886 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51801, d66886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51801, d66886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51802 q = 1) (hb : d66279 q = 1) : d66887 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51802, d66887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51802, d66887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2615 q = 1) (hb : d66279 q = 1) : d2615 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54576 q = 1) (hb : d66279 q = 1) : d66888 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54576, d66888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54576, d66888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54577 q = 1) (hb : d66279 q = 1) : d66889 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54577, d66889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54577, d66889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro3485 (p : Pattern) (ha : d54583 p = 1) (hb : d66279 p = 1) : d66895 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66279 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54578 q = 1) (hb : d66279 q = 1) : d66890 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54578, d66890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54578, d66890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3484 q ha hb
  have h2 (q : Pattern) (ha : d54579 q = 1) (hb : d66279 q = 1) : d66891 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54579, d66891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54579, d66891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54580 q = 1) (hb : d66279 q = 1) : d66892 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54580, d66892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54580, d66892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54581 q = 1) (hb : d66279 q = 1) : d66893 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54581, d66893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54581, d66893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54582 q = 1) (hb : d66279 q = 1) : d66894 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54582, d66894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54582, d66894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54583 q = 1) (hb : d66279 q = 1) : d66895 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54583, d66895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54583, d66895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro3486 (p : Pattern) (ha : d54589 p = 1) (hb : d66279 p = 1) : d66901 p = 1 := by
  have h0 (q : Pattern) (ha : d54542 q = 1) (hb : d66279 q = 1) : d66822 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54542, d66822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3465 q ha hb
    | true =>
      simp only [d54542, d66822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3469 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d66279 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54551 q = 1) (hb : d66279 q = 1) : d66839 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54551, d66839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54551, d66839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3473 q ha hb
  have h3 (q : Pattern) (ha : d54552 q = 1) (hb : d66279 q = 1) : d66840 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54552, d66840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54552, d66840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54561 q = 1) (hb : d66279 q = 1) : d66857 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54561, d66857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54561, d66857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3477 q ha hb
  have h5 (q : Pattern) (ha : d54562 q = 1) (hb : d66279 q = 1) : d66858 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54562, d66858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54562, d66858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54563 q = 1) (hb : d66279 q = 1) : d66859 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54563, d66859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54563, d66859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54572 q = 1) (hb : d66279 q = 1) : d66876 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54572, d66876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54572, d66876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3481 q ha hb
  have h8 (q : Pattern) (ha : d54573 q = 1) (hb : d66279 q = 1) : d66877 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54573, d66877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54573, d66877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54574 q = 1) (hb : d66279 q = 1) : d66878 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54574, d66878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54574, d66878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54575 q = 1) (hb : d66279 q = 1) : d66879 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54575, d66879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54575, d66879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54584 q = 1) (hb : d66279 q = 1) : d66896 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54584, d66896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54584, d66896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3485 q ha hb
  have h12 (q : Pattern) (ha : d54585 q = 1) (hb : d66279 q = 1) : d66897 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54585, d66897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54585, d66897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54586 q = 1) (hb : d66279 q = 1) : d66898 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54586, d66898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54586, d66898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54587 q = 1) (hb : d66279 q = 1) : d66899 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54587, d66899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54587, d66899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54588 q = 1) (hb : d66279 q = 1) : d66900 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54588, d66900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54588, d66900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54589 q = 1) (hb : d66279 q = 1) : d66901 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d54589, d66901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54589, d66901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro3487 (p : Pattern) (ha : d54595 p = 1) (hb : d66279 p = 1) : d66907 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66279 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54590 q = 1) (hb : d66279 q = 1) : d66902 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54590, d66902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3486 q ha hb
    | true =>
      simp only [d54590, d66902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54591 q = 1) (hb : d66279 q = 1) : d66903 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54591, d66903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54591, d66903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54592 q = 1) (hb : d66279 q = 1) : d66904 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54592, d66904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54592, d66904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54593 q = 1) (hb : d66279 q = 1) : d66905 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54593, d66905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54593, d66905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54594 q = 1) (hb : d66279 q = 1) : d66906 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54594, d66906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54594, d66906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54595 q = 1) (hb : d66279 q = 1) : d66907 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d54595, d66907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54595, d66907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3488 (p : Pattern) (ha : d54601 p = 1) (hb : d66279 p = 1) : d66913 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66279 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54596 q = 1) (hb : d66279 q = 1) : d66908 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54596, d66908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3487 q ha hb
    | true =>
      simp only [d54596, d66908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54597 q = 1) (hb : d66279 q = 1) : d66909 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54597, d66909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54597, d66909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54598 q = 1) (hb : d66279 q = 1) : d66910 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54598, d66910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54598, d66910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54599 q = 1) (hb : d66279 q = 1) : d66911 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54599, d66911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54599, d66911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54600 q = 1) (hb : d66279 q = 1) : d66912 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54600, d66912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54600, d66912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54601 q = 1) (hb : d66279 q = 1) : d66913 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d54601, d66913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54601, d66913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3489 (p : Pattern) (ha : d54607 p = 1) (hb : d66279 p = 1) : d66919 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66279 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54602 q = 1) (hb : d66279 q = 1) : d66914 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54602, d66914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3488 q ha hb
    | true =>
      simp only [d54602, d66914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54603 q = 1) (hb : d66279 q = 1) : d66915 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54603, d66915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54603, d66915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54604 q = 1) (hb : d66279 q = 1) : d66916 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54604, d66916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54604, d66916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54605 q = 1) (hb : d66279 q = 1) : d66917 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54605, d66917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54605, d66917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54606 q = 1) (hb : d66279 q = 1) : d66918 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54606, d66918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54606, d66918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54607 q = 1) (hb : d66279 q = 1) : d66919 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d54607, d66919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54607, d66919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3490 (p : Pattern) (ha : d54613 p = 1) (hb : d66279 p = 1) : d66925 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66279 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54608 q = 1) (hb : d66279 q = 1) : d66920 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54608, d66920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3489 q ha hb
    | true =>
      simp only [d54608, d66920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54609 q = 1) (hb : d66279 q = 1) : d66921 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54609, d66921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54609, d66921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54610 q = 1) (hb : d66279 q = 1) : d66922 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54610, d66922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54610, d66922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54611 q = 1) (hb : d66279 q = 1) : d66923 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54611, d66923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54611, d66923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54612 q = 1) (hb : d66279 q = 1) : d66924 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54612, d66924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54612, d66924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54613 q = 1) (hb : d66279 q = 1) : d66925 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d54613, d66925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54613, d66925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3491 (p : Pattern) (ha : d54619 p = 1) (hb : d66279 p = 1) : d66931 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66279 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54614 q = 1) (hb : d66279 q = 1) : d66926 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54614, d66926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3490 q ha hb
    | true =>
      simp only [d54614, d66926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54615 q = 1) (hb : d66279 q = 1) : d66927 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54615, d66927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54615, d66927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54616 q = 1) (hb : d66279 q = 1) : d66928 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54616, d66928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54616, d66928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54617 q = 1) (hb : d66279 q = 1) : d66929 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54617, d66929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54617, d66929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54618 q = 1) (hb : d66279 q = 1) : d66930 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54618, d66930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54618, d66930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54619 q = 1) (hb : d66279 q = 1) : d66931 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d54619, d66931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54619, d66931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3492 (p : Pattern) (ha : d54625 p = 1) (hb : d66280 p = 1) : d66937 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66279 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54620 q = 1) (hb : d66279 q = 1) : d66932 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54620, d66932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3491 q ha hb
    | true =>
      simp only [d54620, d66932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54621 q = 1) (hb : d66279 q = 1) : d66933 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54621, d66933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54621, d66933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54622 q = 1) (hb : d66279 q = 1) : d66934 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54622, d66934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54622, d66934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d54623 q = 1) (hb : d66280 q = 1) : d66935 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54623, d66280, d66935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54623, d66280, d66935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d66280 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d54624 q = 1) (hb : d66280 q = 1) : d66936 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54624, d66936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54624, d66936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54625 q = 1) (hb : d66280 q = 1) : d66937 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54625, d66937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54625, d66937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro3493 (p : Pattern) (ha : d54631 p = 1) (hb : d66280 p = 1) : d66943 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66280 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54626 q = 1) (hb : d66280 q = 1) : d66938 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54626, d66938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3492 q ha hb
    | true =>
      simp only [d54626, d66938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54627 q = 1) (hb : d66280 q = 1) : d66939 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54627, d66939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54627, d66939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54628 q = 1) (hb : d66280 q = 1) : d66940 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54628, d66940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54628, d66940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54629 q = 1) (hb : d66280 q = 1) : d66941 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54629, d66941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54629, d66941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54630 q = 1) (hb : d66280 q = 1) : d66942 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54630, d66942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54630, d66942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54631 q = 1) (hb : d66280 q = 1) : d66943 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54631, d66943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54631, d66943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro3494 (p : Pattern) (ha : d66774 p = 1) (hb : d66943 p = 1) : d66943 p = 1 := by
  have h0 (q : Pattern) (ha : d66774 q = 1) (hb : d66943 q = 1) : d66943 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro3495 (p : Pattern) (ha : d54976 p = 1) (hb : d66280 p = 1) : d54976 p = 1 := by
  have h0 (q : Pattern) (ha : d54976 q = 1) (hb : d66280 q = 1) : d54976 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro3496 (p : Pattern) (ha : d42 p = 1) (hb : d66529 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d51891 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, d51891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, d51891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51891 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d40 q = 1) (hb : d51891 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d41 q = 1) (hb : d66528 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, d66528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d41, d66528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42 q = 1) (hb : d66529 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42, d66529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42, d66529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro3497 (p : Pattern) (ha : d104 p = 1) (hb : d66534 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d66532 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d43 q = 1) (hb : d66530 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d66530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3496 q ha hb
    | true =>
      simp only [d43, d66530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d100 q = 1) (hb : d66531 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d66531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, d66531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101 q = 1) (hb : d66532 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d66532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101, d66532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102 q = 1) (hb : d66532 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d103 q = 1) (hb : d66533 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d66533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d66533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d104 q = 1) (hb : d66534 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, d66534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, d66534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro3498 (p : Pattern) (ha : d49 p = 1) (hb : d66535 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d51891 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, d51891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, d51891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51891 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d40 q = 1) (hb : d51891 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d41 q = 1) (hb : d66528 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, d66528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d41, d66528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d66535 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d49, d66535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d49, d66535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro3499 (p : Pattern) (ha : d111 p = 1) (hb : d66540 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d66532 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d43 q = 1) (hb : d66530 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d66530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3496 q ha hb
    | true =>
      simp only [d43, d66530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d100 q = 1) (hb : d66531 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d66531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, d66531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101 q = 1) (hb : d66532 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d66532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101, d66532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102 q = 1) (hb : d66532 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d103 q = 1) (hb : d66533 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d66533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d66533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d66538 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d50 q = 1) (hb : d66536 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d66536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3498 q ha hb
    | true =>
      simp only [d50, d66536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d107 q = 1) (hb : d66537 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d66537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107, d66537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108 q = 1) (hb : d66538 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d66538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108, d66538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d109 q = 1) (hb : d66538 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d110 q = 1) (hb : d66539 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d66539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, d66539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d111 q = 1) (hb : d66540 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, d66540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d111, d66540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
end NetHack.Soko22Hazard87
