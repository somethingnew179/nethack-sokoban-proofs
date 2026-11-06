import NetHack.Soko22Hazard87.EqIntroBlocks0034
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro8750 (p : Pattern) (selected : d8878 p = 2) : d94618 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8873 q = 2) : d8883 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8873, d8883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8749 q selected
    | true =>
      simp only [d8873, d8883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8874 q = 2) : d8884 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8874, d8884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8874, d8884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1475 q = 2) : d1431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1475, d1431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro910 q selected
    | true =>
      simp only [d1475, d1431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1476 q = 2) : d1432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1476, d1432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1476, d1432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8875 q = 2) : d94615 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8875, d94615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8875, d94615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8876 q = 2) : d94616 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8876, d94616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8876, d94616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d8877 q = 2) : d94617 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8877, d94617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8877, d94617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8878 q = 2) : d94618 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8878, d94618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8878, d94618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8751 (p : Pattern) (selected : d8882 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1402 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro898 q selected
    | true =>
      simp only [d1402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro899 q selected
  have h2 (q : Pattern) (selected : d1403 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1404 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7000 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1412 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro899 q selected
    | true =>
      simp only [d1412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro900 q selected
  have h6 (q : Pattern) (selected : d1413 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1414 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d1420 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d8881 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d8882 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d8882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro8752 (p : Pattern) (selected : d8888 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8883 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8751 q selected
    | true =>
      simp only [d8883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8884 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d8885 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8886 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d8887 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d8888 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8753 (p : Pattern) (selected : d8894 p = 2) : d94624 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8869 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8747 q selected
    | true =>
      simp only [d8869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8748 q selected
  have h2 (q : Pattern) (selected : d8879 q = 2) : d94619 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8879, d94619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8750 q selected
    | true =>
      simp only [d8879, d94619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro912 q selected
  have h3 (q : Pattern) (selected : d8880 q = 2) : d94620 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8880, d94620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8880, d94620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d8889 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8752 q selected
    | true =>
      simp only [d8889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d8890 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d8891 q = 2) : d94621 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8891, d94621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8891, d94621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d8892 q = 2) : d94622 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8892, d94622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8892, d94622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d8893 q = 2) : d94623 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8893, d94623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8893, d94623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d8894 q = 2) : d94624 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8894, d94624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8894, d94624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro8754 (p : Pattern) (selected : d8900 p = 2) : d94630 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8756 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8725 q selected
  have h2 (q : Pattern) (selected : d8757 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d8765 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8725 q selected
    | true =>
      simp only [d8765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8727 q selected
  have h4 (q : Pattern) (selected : d8766 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d8767 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8837 q = 2) : d8765 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8837, d8765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8736 q selected
    | true =>
      simp only [d8837, d8765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8743 q selected
  have h7 (q : Pattern) (selected : d8844 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8744 q selected
    | true =>
      simp only [d8844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro894 q selected
  have h8 (q : Pattern) (selected : d8845 q = 2) : d8766 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8845, d8766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8845, d8766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d8846 q = 2) : d94607 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8846, d94607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d8846, d94607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d8847 q = 2) : d94608 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d8847, d94608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8847, d94608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d8851 q = 2) : d94610 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8851, d94610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8851, d94610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8745 q selected
  have h12 (q : Pattern) (selected : d1371 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro896 q selected
  have h13 (q : Pattern) (selected : d8852 q = 2) : d94611 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8852, d94611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d8852, d94611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d8853 q = 2) : d94612 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8853, d94612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d8853, d94612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d8854 q = 2) : d94613 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d8854, d94613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d8854, d94613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d8855 q = 2) : d94614 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d8855, d94614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d8855, d94614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d8895 q = 2) : d94625 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8895, d94625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8895, d94625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8753 q selected
  have h18 (q : Pattern) (selected : d1504 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro915 q selected
  have h19 (q : Pattern) (selected : d8896 q = 2) : d94626 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8896, d94626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d8896, d94626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d8897 q = 2) : d94627 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8897, d94627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d8897, d94627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d8898 q = 2) : d94628 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d8898, d94628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d8898, d94628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d8899 q = 2) : d94629 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d8899, d94629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d8899, d94629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d8900 q = 2) : d94630 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d8900, d94630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d8900, d94630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro8755 (p : Pattern) (selected : d8906 p = 2) : d94636 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8901 q = 2) : d94631 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d8901, d94631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8901, d94631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8754 q selected
  have h2 (q : Pattern) (selected : d8902 q = 2) : d94632 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d8902, d94632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8902, d94632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d8903 q = 2) : d94633 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d8903, d94633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8903, d94633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d8904 q = 2) : d94634 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d8904, d94634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8904, d94634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8905 q = 2) : d94635 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d8905, d94635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8905, d94635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8906 q = 2) : d94636 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d8906, d94636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8906, d94636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro8756 (p : Pattern) (selected : d8911 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1590 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro929 q selected
    | true =>
      simp only [d1590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro930 q selected
  have h2 (q : Pattern) (selected : d1591 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1592 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7034 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1603 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro930 q selected
    | true =>
      simp only [d1603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro932 q selected
  have h6 (q : Pattern) (selected : d1604 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1605 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d1607 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d8910 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d8911 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d8911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro8757 (p : Pattern) (selected : d8917 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8912 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8756 q selected
    | true =>
      simp only [d8912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8913 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1614 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro934 q selected
    | true =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1615 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8914 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8915 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d8916 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8917 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro8758 (p : Pattern) (selected : d8923 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8918 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8757 q selected
    | true =>
      simp only [d8918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro936 q selected
  have h2 (q : Pattern) (selected : d8919 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d8920 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8921 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8922 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8923 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro8759 (p : Pattern) (selected : d8926 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8912 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8756 q selected
    | true =>
      simp only [d8912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8913 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1614 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro934 q selected
    | true =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1615 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8914 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8915 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d8916 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8926 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8760 (p : Pattern) (selected : d8932 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8918 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8757 q selected
    | true =>
      simp only [d8918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro936 q selected
  have h2 (q : Pattern) (selected : d8919 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d8920 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8921 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8922 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8927 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8759 q selected
    | true =>
      simp only [d8927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro939 q selected
  have h7 (q : Pattern) (selected : d8928 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d8929 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d8930 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d8931 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d8932 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro8761 (p : Pattern) (selected : d8937 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8912 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8756 q selected
    | true =>
      simp only [d8912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8913 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1614 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro934 q selected
    | true =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1615 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8914 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8915 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d8936 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d8937 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro8762 (p : Pattern) (selected : d8944 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8912 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8756 q selected
    | true =>
      simp only [d8912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8913 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1614 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro934 q selected
    | true =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1615 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8914 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8942 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d8943 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8944 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro8763 (p : Pattern) (selected : d8950 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1671 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro946 q selected
    | true =>
      simp only [d1671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro929 q selected
  have h2 (q : Pattern) (selected : d1672 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1673 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d8948 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1590 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro929 q selected
    | true =>
      simp only [d1590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro930 q selected
  have h6 (q : Pattern) (selected : d1591 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1592 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7034 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d8949 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d8950 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d8950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro8764 (p : Pattern) (selected : d8956 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8951 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8763 q selected
    | true =>
      simp only [d8951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8952 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7037 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5963 q selected
    | true =>
      simp only [d7037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7038 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8953 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8954 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d8955 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8956 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro8765 (p : Pattern) (selected : d8960 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7037 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5963 q selected
    | true =>
      simp only [d7037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7038 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1614 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro934 q selected
    | true =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1615 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8957 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8958 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d8959 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8960 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro8766 (p : Pattern) (selected : d8964 p = 2) : d8911 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1761 q = 2) : d1590 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1761, d1590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro962 q selected
    | true =>
      simp only [d1761, d1590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro963 q selected
  have h2 (q : Pattern) (selected : d1762 q = 2) : d1591 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1762, d1591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1762, d1591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1763 q = 2) : d1592 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1763, d1592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1763, d1592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d8962 q = 2) : d7034 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8962, d7034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8962, d7034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1774 q = 2) : d1603 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1774, d1603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro963 q selected
    | true =>
      simp only [d1774, d1603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro965 q selected
  have h6 (q : Pattern) (selected : d1775 q = 2) : d1604 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1775, d1604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1775, d1604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1776 q = 2) : d1605 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1776, d1605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1776, d1605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d1778 q = 2) : d1607 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1778, d1607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1778, d1607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d8963 q = 2) : d8910 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8963, d8910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8963, d8910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d8964 q = 2) : d8911 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8964, d8911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d8964, d8911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro8767 (p : Pattern) (selected : d8970 p = 2) : d8917 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8965 q = 2) : d8912 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8965, d8912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8766 q selected
    | true =>
      simp only [d8965, d8912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8966 q = 2) : d8913 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8966, d8913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8966, d8913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1785 q = 2) : d1614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1785, d1614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro967 q selected
    | true =>
      simp only [d1785, d1614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1786 q = 2) : d1615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1786, d1615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1786, d1615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8967 q = 2) : d8914 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8967, d8914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8967, d8914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8968 q = 2) : d8915 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8968, d8915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8968, d8915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d8969 q = 2) : d8916 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8969, d8916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8969, d8916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8970 q = 2) : d8917 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8970, d8917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8970, d8917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro8768 (p : Pattern) (selected : d8976 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8912 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8756 q selected
    | true =>
      simp only [d8912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8913 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d8973 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8974 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d8975 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d8976 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro8769 (p : Pattern) (selected : d8982 p = 2) : d8923 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8938 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8761 q selected
    | true =>
      simp only [d8938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro942 q selected
  have h2 (q : Pattern) (selected : d8939 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d8940 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8941 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8945 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8762 q selected
    | true =>
      simp only [d8945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro944 q selected
  have h6 (q : Pattern) (selected : d8946 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d8947 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8961 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8764 q selected
    | true =>
      simp only [d8961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8765 q selected
  have h9 (q : Pattern) (selected : d8971 q = 2) : d8918 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8971, d8918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8767 q selected
    | true =>
      simp only [d8971, d8918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro969 q selected
  have h10 (q : Pattern) (selected : d8972 q = 2) : d8919 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8972, d8919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d8972, d8919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d8977 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8768 q selected
    | true =>
      simp only [d8977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d8978 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d8978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d8979 q = 2) : d8920 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8979, d8920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d8979, d8920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d8980 q = 2) : d8921 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8980, d8921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8980, d8921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d8981 q = 2) : d8922 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8981, d8922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8981, d8922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d8982 q = 2) : d8923 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8982, d8923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8982, d8923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro8770 (p : Pattern) (selected : d8983 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8912 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8756 q selected
    | true =>
      simp only [d8912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8913 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1614 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro934 q selected
    | true =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1615 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8914 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8915 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d8936 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d8983 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8771 (p : Pattern) (selected : d8988 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8912 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8756 q selected
    | true =>
      simp only [d8912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8913 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1614 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro934 q selected
    | true =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1615 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8914 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8942 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d8943 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8988 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8772 (p : Pattern) (selected : d8992 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8951 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8763 q selected
    | true =>
      simp only [d8951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8952 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7037 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5963 q selected
    | true =>
      simp only [d7037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7038 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8953 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8954 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d8955 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8992 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8773 (p : Pattern) (selected : d8993 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7037 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5963 q selected
    | true =>
      simp only [d7037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7038 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1614 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro934 q selected
    | true =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1615 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8957 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8958 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d8959 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8993 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8774 (p : Pattern) (selected : d8995 p = 2) : d8926 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8965 q = 2) : d8912 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8965, d8912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8766 q selected
    | true =>
      simp only [d8965, d8912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8966 q = 2) : d8913 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8966, d8913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8966, d8913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1785 q = 2) : d1614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1785, d1614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro967 q selected
    | true =>
      simp only [d1785, d1614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1786 q = 2) : d1615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1786, d1615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1786, d1615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8967 q = 2) : d8914 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8967, d8914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8967, d8914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8968 q = 2) : d8915 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8968, d8915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8968, d8915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d8969 q = 2) : d8916 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8969, d8916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8969, d8916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8995 q = 2) : d8926 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8995, d8926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8995, d8926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8775 (p : Pattern) (selected : d8998 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8912 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8756 q selected
    | true =>
      simp only [d8912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8913 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d8973 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8974 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d8975 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d8998 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8776 (p : Pattern) (selected : d9004 p = 2) : d8932 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8938 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8761 q selected
    | true =>
      simp only [d8938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro942 q selected
  have h2 (q : Pattern) (selected : d8939 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d8940 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8941 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8945 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8762 q selected
    | true =>
      simp only [d8945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro944 q selected
  have h6 (q : Pattern) (selected : d8946 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d8947 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8961 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8764 q selected
    | true =>
      simp only [d8961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8765 q selected
  have h9 (q : Pattern) (selected : d8971 q = 2) : d8918 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8971, d8918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8767 q selected
    | true =>
      simp only [d8971, d8918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro969 q selected
  have h10 (q : Pattern) (selected : d8972 q = 2) : d8919 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8972, d8919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d8972, d8919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d8977 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8768 q selected
    | true =>
      simp only [d8977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d8978 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d8978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d8979 q = 2) : d8920 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8979, d8920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d8979, d8920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d8980 q = 2) : d8921 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8980, d8921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8980, d8921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d8981 q = 2) : d8922 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8981, d8922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8981, d8922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d8984 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8770 q selected
    | true =>
      simp only [d8984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro972 q selected
  have h17 (q : Pattern) (selected : d8985 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d8986 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d8986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d8987 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d8989 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8771 q selected
    | true =>
      simp only [d8989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro974 q selected
  have h21 (q : Pattern) (selected : d8990 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d8991 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d8991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d8994 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8772 q selected
    | true =>
      simp only [d8994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8773 q selected
  have h24 (q : Pattern) (selected : d8996 q = 2) : d8927 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8996, d8927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8774 q selected
    | true =>
      simp only [d8996, d8927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro977 q selected
  have h25 (q : Pattern) (selected : d8997 q = 2) : d8928 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8997, d8928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d8997, d8928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d8999 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8775 q selected
    | true =>
      simp only [d8999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d9000 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d9000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d9001 q = 2) : d8929 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9001, d8929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d9001, d8929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d9002 q = 2) : d8930 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9002, d8930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d9002, d8930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d9003 q = 2) : d8931 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9003, d8931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d9003, d8931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d9004 q = 2) : d8932 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9004, d8932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d9004, d8932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro8777 (p : Pattern) (selected : d9011 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d9006 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8765 q selected
    | true =>
      simp only [d9006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro936 q selected
  have h2 (q : Pattern) (selected : d9007 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d9008 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9009 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d9010 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1827 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro936 q selected
    | true =>
      simp only [d1827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1828 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d1829 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1830 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d1831 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d9011 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro8778 (p : Pattern) (selected : d9018 p = 2) : d94642 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8994 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8772 q selected
    | true =>
      simp only [d8994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8773 q selected
  have h2 (q : Pattern) (selected : d8996 q = 2) : d8927 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8996, d8927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8774 q selected
    | true =>
      simp only [d8996, d8927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro977 q selected
  have h3 (q : Pattern) (selected : d8997 q = 2) : d8928 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8997, d8928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8997, d8928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d8999 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8775 q selected
    | true =>
      simp only [d8999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9000 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9001 q = 2) : d8929 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9001, d8929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9001, d8929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d9016 q = 2) : d8930 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9016, d8930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9016, d8930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d9017 q = 2) : d8931 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9017, d8931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9017, d8931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d9018 q = 2) : d94642 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9018, d94642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9018, d94642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro8779 (p : Pattern) (selected : d9026 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1874 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro983 q selected
    | true =>
      simp only [d1874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro984 q selected
  have h2 (q : Pattern) (selected : d1875 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1876 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9024 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1879 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro984 q selected
    | true =>
      simp only [d1879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro985 q selected
  have h6 (q : Pattern) (selected : d1880 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1881 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7080 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d9025 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d9026 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d9026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro8780 (p : Pattern) (selected : d9032 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d9027 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8779 q selected
    | true =>
      simp only [d9027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9028 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7083 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5972 q selected
    | true =>
      simp only [d7083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7084 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d9029 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9030 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9031 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9032 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d9032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8781 (p : Pattern) (selected : d9036 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7083 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5972 q selected
    | true =>
      simp only [d7083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7084 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1908 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro990 q selected
    | true =>
      simp only [d1908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1909 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d9033 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9034 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9035 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9036 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d9036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8782 (p : Pattern) (selected : d9040 p = 2) : d9050 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1932 q = 2) : d1879 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1932, d1879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro992 q selected
    | true =>
      simp only [d1932, d1879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro993 q selected
  have h2 (q : Pattern) (selected : d1933 q = 2) : d1880 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1933, d1880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1933, d1880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1934 q = 2) : d1881 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1934, d1881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1934, d1881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9038 q = 2) : d7080 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9038, d7080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9038, d7080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1941 q = 2) : d1889 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1941, d1889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro993 q selected
    | true =>
      simp only [d1941, d1889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro994 q selected
  have h6 (q : Pattern) (selected : d1942 q = 2) : d1890 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1942, d1890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1942, d1890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1943 q = 2) : d1891 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1943, d1891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1943, d1891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d1945 q = 2) : d1897 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1945, d1897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1945, d1897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d9039 q = 2) : d9049 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9039, d9049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9039, d9049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d9040 q = 2) : d9050 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9040, d9050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d9040, d9050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro8783 (p : Pattern) (selected : d9046 p = 2) : d94651 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d9041 q = 2) : d9051 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9041, d9051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8782 q selected
    | true =>
      simp only [d9041, d9051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9042 q = 2) : d9052 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9042, d9052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9042, d9052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1952 q = 2) : d1908 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1952, d1908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro996 q selected
    | true =>
      simp only [d1952, d1908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1953 q = 2) : d1909 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1953, d1909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1953, d1909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d9043 q = 2) : d94648 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9043, d94648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9043, d94648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9044 q = 2) : d94649 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9044, d94649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9044, d94649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9045 q = 2) : d94650 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9045, d94650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9045, d94650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9046 q = 2) : d94651 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9046, d94651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d9046, d94651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8784 (p : Pattern) (selected : d9050 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1879 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro984 q selected
    | true =>
      simp only [d1879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro985 q selected
  have h2 (q : Pattern) (selected : d1880 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1881 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7080 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1889 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro985 q selected
    | true =>
      simp only [d1889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro986 q selected
  have h6 (q : Pattern) (selected : d1890 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1891 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d1897 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d9049 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d9050 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d9050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro8785 (p : Pattern) (selected : d9056 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d9051 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8784 q selected
    | true =>
      simp only [d9051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9052 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d9053 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9054 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9055 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9056 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8786 (p : Pattern) (selected : d9062 p = 2) : d94657 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d9037 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8780 q selected
    | true =>
      simp only [d9037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8781 q selected
  have h2 (q : Pattern) (selected : d9047 q = 2) : d94652 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9047, d94652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8783 q selected
    | true =>
      simp only [d9047, d94652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro998 q selected
  have h3 (q : Pattern) (selected : d9048 q = 2) : d94653 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9048, d94653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9048, d94653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9057 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8785 q selected
    | true =>
      simp only [d9057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9058 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9059 q = 2) : d94654 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9059, d94654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9059, d94654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d9060 q = 2) : d94655 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9060, d94655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9060, d94655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d9061 q = 2) : d94656 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9061, d94656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9061, d94656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d9062 q = 2) : d94657 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9062, d94657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9062, d94657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro8787 (p : Pattern) (selected : d9068 p = 2) : d94663 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8924 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8758 q selected
  have h2 (q : Pattern) (selected : d8925 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d8933 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8758 q selected
    | true =>
      simp only [d8933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8760 q selected
  have h4 (q : Pattern) (selected : d8934 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d8935 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9005 q = 2) : d8933 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9005, d8933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8769 q selected
    | true =>
      simp only [d9005, d8933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8776 q selected
  have h7 (q : Pattern) (selected : d9012 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8777 q selected
    | true =>
      simp only [d9012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro980 q selected
  have h8 (q : Pattern) (selected : d9013 q = 2) : d8934 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d9013, d8934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9013, d8934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d9014 q = 2) : d94640 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d9014, d94640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9014, d94640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d9015 q = 2) : d94641 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d9015, d94641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9015, d94641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d9019 q = 2) : d94643 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9019, d94643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9019, d94643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8778 q selected
  have h12 (q : Pattern) (selected : d1848 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro982 q selected
  have h13 (q : Pattern) (selected : d9020 q = 2) : d94644 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d9020, d94644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d9020, d94644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d9021 q = 2) : d94645 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d9021, d94645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d9021, d94645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d9022 q = 2) : d94646 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d9022, d94646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d9022, d94646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d9023 q = 2) : d94647 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d9023, d94647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d9023, d94647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d9063 q = 2) : d94658 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9063, d94658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9063, d94658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8786 q selected
  have h18 (q : Pattern) (selected : d1981 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1001 q selected
  have h19 (q : Pattern) (selected : d9064 q = 2) : d94659 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d9064, d94659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d9064, d94659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d9065 q = 2) : d94660 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d9065, d94660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d9065, d94660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d9066 q = 2) : d94661 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d9066, d94661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d9066, d94661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d9067 q = 2) : d94662 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d9067, d94662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d9067, d94662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d9068 q = 2) : d94663 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d9068, d94663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d9068, d94663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro8788 (p : Pattern) (selected : d9074 p = 2) : d94669 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d9069 q = 2) : d94664 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d9069, d94664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9069, d94664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8787 q selected
  have h2 (q : Pattern) (selected : d9070 q = 2) : d94665 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d9070, d94665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9070, d94665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d9071 q = 2) : d94666 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d9071, d94666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9071, d94666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9072 q = 2) : d94667 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d9072, d94667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9072, d94667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d9073 q = 2) : d94668 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d9073, d94668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9073, d94668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9074 q = 2) : d94669 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d9074, d94669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9074, d94669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro8789 (p : Pattern) (selected : d9080 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2073 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1018 q selected
    | true =>
      simp only [d2073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1019 q selected
  have h2 (q : Pattern) (selected : d2074 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2075 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7115 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2086 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1019 q selected
    | true =>
      simp only [d2086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1021 q selected
  have h6 (q : Pattern) (selected : d2087 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2088 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d2090 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d2090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d9079 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d9080 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d9080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro8790 (p : Pattern) (selected : d9086 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d9081 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8789 q selected
    | true =>
      simp only [d9081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9082 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2097 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1023 q selected
    | true =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2098 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d9083 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9084 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9085 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9086 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro8791 (p : Pattern) (selected : d9092 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d9087 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8790 q selected
    | true =>
      simp only [d9087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1025 q selected
  have h2 (q : Pattern) (selected : d9088 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d9089 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9090 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d9091 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9092 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro8792 (p : Pattern) (selected : d9095 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d9081 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8789 q selected
    | true =>
      simp only [d9081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9082 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2097 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1023 q selected
    | true =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2098 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d9083 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9084 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9085 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9095 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d9095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8793 (p : Pattern) (selected : d9101 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d9087 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8790 q selected
    | true =>
      simp only [d9087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1025 q selected
  have h2 (q : Pattern) (selected : d9088 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d9089 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9090 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d9091 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9096 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8792 q selected
    | true =>
      simp only [d9096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1028 q selected
  have h7 (q : Pattern) (selected : d9097 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d9098 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d9098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d9099 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d9100 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d9101 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro8794 (p : Pattern) (selected : d9106 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d9081 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8789 q selected
    | true =>
      simp only [d9081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9082 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2097 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1023 q selected
    | true =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2098 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d9083 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9084 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9105 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d9106 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro8795 (p : Pattern) (selected : d9113 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d9081 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8789 q selected
    | true =>
      simp only [d9081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9082 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2097 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1023 q selected
    | true =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2098 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d9083 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9111 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d9112 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9113 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro8796 (p : Pattern) (selected : d9119 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2150 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1035 q selected
    | true =>
      simp only [d2150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1018 q selected
  have h2 (q : Pattern) (selected : d2151 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2152 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9117 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2073 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1018 q selected
    | true =>
      simp only [d2073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1019 q selected
  have h6 (q : Pattern) (selected : d2074 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2075 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7115 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d9118 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d9119 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d9119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro8797 (p : Pattern) (selected : d9125 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d9120 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8796 q selected
    | true =>
      simp only [d9120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9121 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7118 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5978 q selected
    | true =>
      simp only [d7118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7119 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d9122 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9123 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9124 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9125 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro8798 (p : Pattern) (selected : d9129 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7118 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5978 q selected
    | true =>
      simp only [d7118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7119 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2097 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1023 q selected
    | true =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2098 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d9126 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9127 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9128 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9129 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro8799 (p : Pattern) (selected : d9133 p = 2) : d9080 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2239 q = 2) : d2073 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2239, d2073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1052 q selected
    | true =>
      simp only [d2239, d2073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1053 q selected
  have h2 (q : Pattern) (selected : d2240 q = 2) : d2074 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2240, d2074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2240, d2074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2241 q = 2) : d2075 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2241, d2075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2241, d2075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9131 q = 2) : d7115 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9131, d7115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9131, d7115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2252 q = 2) : d2086 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2252, d2086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1053 q selected
    | true =>
      simp only [d2252, d2086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1055 q selected
  have h6 (q : Pattern) (selected : d2253 q = 2) : d2087 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2253, d2087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2253, d2087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2254 q = 2) : d2088 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2254, d2088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2254, d2088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d2256 q = 2) : d2090 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2256, d2090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d2256, d2090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d9132 q = 2) : d9079 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9132, d9079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9132, d9079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d9133 q = 2) : d9080 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9133, d9080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d9133, d9080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro8800 (p : Pattern) (selected : d9139 p = 2) : d9086 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d9134 q = 2) : d9081 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9134, d9081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8799 q selected
    | true =>
      simp only [d9134, d9081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9135 q = 2) : d9082 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9135, d9082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9135, d9082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2263 q = 2) : d2097 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2263, d2097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1057 q selected
    | true =>
      simp only [d2263, d2097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2264 q = 2) : d2098 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2264, d2098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2264, d2098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d9136 q = 2) : d9083 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9136, d9083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9136, d9083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9137 q = 2) : d9084 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9137, d9084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9137, d9084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9138 q = 2) : d9085 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9138, d9085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9138, d9085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9139 q = 2) : d9086 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9139, d9086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9139, d9086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro8801 (p : Pattern) (selected : d9145 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d9081 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8789 q selected
    | true =>
      simp only [d9081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9082 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d9142 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9143 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9144 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9145 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro8802 (p : Pattern) (selected : d9151 p = 2) : d9092 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d9107 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8794 q selected
    | true =>
      simp only [d9107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1031 q selected
  have h2 (q : Pattern) (selected : d9108 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d9109 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9110 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d9114 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8795 q selected
    | true =>
      simp only [d9114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1033 q selected
  have h6 (q : Pattern) (selected : d9115 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d9116 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9130 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8797 q selected
    | true =>
      simp only [d9130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8798 q selected
  have h9 (q : Pattern) (selected : d9140 q = 2) : d9087 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9140, d9087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8800 q selected
    | true =>
      simp only [d9140, d9087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1059 q selected
  have h10 (q : Pattern) (selected : d9141 q = 2) : d9088 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9141, d9088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9141, d9088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d9146 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8801 q selected
    | true =>
      simp only [d9146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d9147 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d9147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d9148 q = 2) : d9089 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9148, d9089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d9148, d9089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d9149 q = 2) : d9090 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9149, d9090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d9149, d9090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d9150 q = 2) : d9091 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9150, d9091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9150, d9091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d9151 q = 2) : d9092 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9151, d9092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9151, d9092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro8803 (p : Pattern) (selected : d9152 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d9081 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8789 q selected
    | true =>
      simp only [d9081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9082 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2097 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1023 q selected
    | true =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2098 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d9083 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9084 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9105 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d9152 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d9152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8804 (p : Pattern) (selected : d9157 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d9081 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8789 q selected
    | true =>
      simp only [d9081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9082 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2097 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1023 q selected
    | true =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2098 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d9083 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9111 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d9112 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9157 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d9157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8805 (p : Pattern) (selected : d9161 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d9120 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8796 q selected
    | true =>
      simp only [d9120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9121 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7118 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5978 q selected
    | true =>
      simp only [d7118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7119 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d9122 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9123 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9124 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9161 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d9161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8806 (p : Pattern) (selected : d9162 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7118 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5978 q selected
    | true =>
      simp only [d7118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7119 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2097 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1023 q selected
    | true =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2098 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d9126 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9127 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9128 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9162 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d9162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8807 (p : Pattern) (selected : d9164 p = 2) : d9095 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d9134 q = 2) : d9081 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9134, d9081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8799 q selected
    | true =>
      simp only [d9134, d9081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9135 q = 2) : d9082 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9135, d9082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9135, d9082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2263 q = 2) : d2097 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2263, d2097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1057 q selected
    | true =>
      simp only [d2263, d2097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2264 q = 2) : d2098 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2264, d2098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2264, d2098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d9136 q = 2) : d9083 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9136, d9083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9136, d9083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9137 q = 2) : d9084 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9137, d9084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9137, d9084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9138 q = 2) : d9085 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9138, d9085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9138, d9085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9164 q = 2) : d9095 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9164, d9095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d9164, d9095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8808 (p : Pattern) (selected : d9167 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d9081 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8789 q selected
    | true =>
      simp only [d9081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9082 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d9142 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9143 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9144 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9167 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8809 (p : Pattern) (selected : d9173 p = 2) : d9101 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d9107 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8794 q selected
    | true =>
      simp only [d9107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1031 q selected
  have h2 (q : Pattern) (selected : d9108 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d9109 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9110 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d9114 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8795 q selected
    | true =>
      simp only [d9114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1033 q selected
  have h6 (q : Pattern) (selected : d9115 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d9116 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9130 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8797 q selected
    | true =>
      simp only [d9130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8798 q selected
  have h9 (q : Pattern) (selected : d9140 q = 2) : d9087 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9140, d9087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8800 q selected
    | true =>
      simp only [d9140, d9087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1059 q selected
  have h10 (q : Pattern) (selected : d9141 q = 2) : d9088 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9141, d9088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9141, d9088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d9146 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8801 q selected
    | true =>
      simp only [d9146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d9147 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d9147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d9148 q = 2) : d9089 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9148, d9089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d9148, d9089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d9149 q = 2) : d9090 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9149, d9090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d9149, d9090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d9150 q = 2) : d9091 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9150, d9091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9150, d9091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d9153 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8803 q selected
    | true =>
      simp only [d9153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1062 q selected
  have h17 (q : Pattern) (selected : d9154 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d9155 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d9155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d9156 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d9158 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8804 q selected
    | true =>
      simp only [d9158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1064 q selected
  have h21 (q : Pattern) (selected : d9159 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d9160 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d9160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d9163 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8805 q selected
    | true =>
      simp only [d9163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8806 q selected
  have h24 (q : Pattern) (selected : d9165 q = 2) : d9096 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9165, d9096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8807 q selected
    | true =>
      simp only [d9165, d9096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1067 q selected
  have h25 (q : Pattern) (selected : d9166 q = 2) : d9097 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9166, d9097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d9166, d9097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d9168 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8808 q selected
    | true =>
      simp only [d9168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d9169 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d9169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d9170 q = 2) : d9098 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9170, d9098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d9170, d9098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d9171 q = 2) : d9099 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9171, d9099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d9171, d9099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d9172 q = 2) : d9100 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9172, d9100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d9172, d9100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d9173 q = 2) : d9101 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9173, d9101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d9173, d9101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro8810 (p : Pattern) (selected : d9180 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d9175 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8798 q selected
    | true =>
      simp only [d9175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1025 q selected
  have h2 (q : Pattern) (selected : d9176 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d9177 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9178 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d9179 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2305 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1025 q selected
    | true =>
      simp only [d2305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2306 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d2307 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d2307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d2308 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d2309 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d9180 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro8811 (p : Pattern) (selected : d9187 p = 2) : d94676 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d9163 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8805 q selected
    | true =>
      simp only [d9163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8806 q selected
  have h2 (q : Pattern) (selected : d9165 q = 2) : d9096 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9165, d9096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8807 q selected
    | true =>
      simp only [d9165, d9096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1067 q selected
  have h3 (q : Pattern) (selected : d9166 q = 2) : d9097 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9166, d9097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9166, d9097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9168 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8808 q selected
    | true =>
      simp only [d9168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9169 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9170 q = 2) : d9098 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9170, d9098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9170, d9098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d9185 q = 2) : d9099 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9185, d9099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9185, d9099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d9186 q = 2) : d9100 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9186, d9100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9186, d9100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d9187 q = 2) : d94676 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9187, d94676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9187, d94676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro8812 (p : Pattern) (selected : d9195 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2352 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1073 q selected
    | true =>
      simp only [d2352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1074 q selected
  have h2 (q : Pattern) (selected : d2353 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2354 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9193 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2357 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1074 q selected
    | true =>
      simp only [d2357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1075 q selected
  have h6 (q : Pattern) (selected : d2358 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2359 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7161 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d9194 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d9195 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d9195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro8813 (p : Pattern) (selected : d9201 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d9196 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8812 q selected
    | true =>
      simp only [d9196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9197 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7164 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5987 q selected
    | true =>
      simp only [d7164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7165 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d9198 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9199 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9200 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9201 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d9201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8814 (p : Pattern) (selected : d9205 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7164 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5987 q selected
    | true =>
      simp only [d7164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7165 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2386 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1080 q selected
    | true =>
      simp only [d2386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2387 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d9202 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9203 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9204 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9205 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d9205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8815 (p : Pattern) (selected : d9209 p = 2) : d9219 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2410 q = 2) : d2357 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2410, d2357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1082 q selected
    | true =>
      simp only [d2410, d2357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1083 q selected
  have h2 (q : Pattern) (selected : d2411 q = 2) : d2358 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2411, d2358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2411, d2358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2412 q = 2) : d2359 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2412, d2359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2412, d2359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9207 q = 2) : d7161 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9207, d7161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9207, d7161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2419 q = 2) : d2367 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2419, d2367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1083 q selected
    | true =>
      simp only [d2419, d2367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1084 q selected
  have h6 (q : Pattern) (selected : d2420 q = 2) : d2368 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2420, d2368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2420, d2368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2421 q = 2) : d2369 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2421, d2369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2421, d2369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d2423 q = 2) : d2375 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2423, d2375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d2423, d2375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d9208 q = 2) : d9218 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9208, d9218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9208, d9218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d9209 q = 2) : d9219 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9209, d9219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d9209, d9219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro8816 (p : Pattern) (selected : d9215 p = 2) : d94685 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d9210 q = 2) : d9220 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9210, d9220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8815 q selected
    | true =>
      simp only [d9210, d9220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9211 q = 2) : d9221 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9211, d9221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9211, d9221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2430 q = 2) : d2386 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2430, d2386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1086 q selected
    | true =>
      simp only [d2430, d2386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2431 q = 2) : d2387 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2431, d2387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2431, d2387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d9212 q = 2) : d94682 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9212, d94682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9212, d94682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9213 q = 2) : d94683 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9213, d94683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9213, d94683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9214 q = 2) : d94684 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9214, d94684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9214, d94684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9215 q = 2) : d94685 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9215, d94685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d9215, d94685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8817 (p : Pattern) (selected : d9219 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2357 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1074 q selected
    | true =>
      simp only [d2357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1075 q selected
  have h2 (q : Pattern) (selected : d2358 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2359 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7161 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2367 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1075 q selected
    | true =>
      simp only [d2367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1076 q selected
  have h6 (q : Pattern) (selected : d2368 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2369 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d2375 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d2375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d9218 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d9219 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d9219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro8818 (p : Pattern) (selected : d9225 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d9220 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8817 q selected
    | true =>
      simp only [d9220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9221 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d9222 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9223 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9224 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9225 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8819 (p : Pattern) (selected : d9231 p = 2) : d94691 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d9206 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8813 q selected
    | true =>
      simp only [d9206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8814 q selected
  have h2 (q : Pattern) (selected : d9216 q = 2) : d94686 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9216, d94686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8816 q selected
    | true =>
      simp only [d9216, d94686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1088 q selected
  have h3 (q : Pattern) (selected : d9217 q = 2) : d94687 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9217, d94687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9217, d94687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9226 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8818 q selected
    | true =>
      simp only [d9226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9227 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9228 q = 2) : d94688 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9228, d94688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9228, d94688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d9229 q = 2) : d94689 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9229, d94689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9229, d94689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d9230 q = 2) : d94690 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9230, d94690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9230, d94690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d9231 q = 2) : d94691 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9231, d94691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9231, d94691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro8820 (p : Pattern) (selected : d9237 p = 2) : d94697 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d9093 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8791 q selected
  have h2 (q : Pattern) (selected : d9094 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d9094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d9102 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8791 q selected
    | true =>
      simp only [d9102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8793 q selected
  have h4 (q : Pattern) (selected : d9103 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d9103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9104 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d9104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9174 q = 2) : d9102 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9174, d9102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8802 q selected
    | true =>
      simp only [d9174, d9102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8809 q selected
  have h7 (q : Pattern) (selected : d9181 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8810 q selected
    | true =>
      simp only [d9181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1070 q selected
  have h8 (q : Pattern) (selected : d9182 q = 2) : d9103 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d9182, d9103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9182, d9103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d9183 q = 2) : d94674 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d9183, d94674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9183, d94674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d9184 q = 2) : d94675 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d9184, d94675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9184, d94675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d9188 q = 2) : d94677 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9188, d94677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9188, d94677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8811 q selected
  have h12 (q : Pattern) (selected : d2326 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1072 q selected
  have h13 (q : Pattern) (selected : d9189 q = 2) : d94678 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d9189, d94678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d9189, d94678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d9190 q = 2) : d94679 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d9190, d94679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d9190, d94679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d9191 q = 2) : d94680 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d9191, d94680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d9191, d94680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d9192 q = 2) : d94681 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d9192, d94681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d9192, d94681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d9232 q = 2) : d94692 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9232, d94692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9232, d94692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8819 q selected
  have h18 (q : Pattern) (selected : d2459 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1091 q selected
  have h19 (q : Pattern) (selected : d9233 q = 2) : d94693 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d9233, d94693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d9233, d94693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d9234 q = 2) : d94694 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d9234, d94694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d9234, d94694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d9235 q = 2) : d94695 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d9235, d94695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d9235, d94695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d9236 q = 2) : d94696 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d9236, d94696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d9236, d94696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d9237 q = 2) : d94697 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d9237, d94697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d9237, d94697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro8821 (p : Pattern) (selected : d9243 p = 2) : d94703 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d9238 q = 2) : d94698 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d9238, d94698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9238, d94698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8820 q selected
  have h2 (q : Pattern) (selected : d9239 q = 2) : d94699 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d9239, d94699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9239, d94699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d9240 q = 2) : d94700 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d9240, d94700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9240, d94700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9241 q = 2) : d94701 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d9241, d94701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9241, d94701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d9242 q = 2) : d94702 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d9242, d94702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9242, d94702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9243 q = 2) : d94703 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d9243, d94703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9243, d94703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro8822 (p : Pattern) (selected : d9249 p = 2) : d94709 p = 1 := by
  have h0 (q : Pattern) (selected : d8574 q = 2) : d94574 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d8574, d94574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8658 q selected
    | true =>
      simp only [d8574, d94574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8689 q selected
  have h1 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h2 (q : Pattern) (selected : d8740 q = 2) : d94605 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d8740, d94605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8740, d94605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8722 q selected
  have h3 (q : Pattern) (selected : d8741 q = 2) : d94606 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d8741, d94606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8741, d94606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d8907 q = 2) : d94637 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d8907, d94637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8907, d94637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8755 q selected
  have h5 (q : Pattern) (selected : d8908 q = 2) : d94638 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d8908, d94638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8908, d94638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8909 q = 2) : d94639 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d8909, d94639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8909, d94639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d9075 q = 2) : d94670 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d9075, d94670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9075, d94670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8788 q selected
  have h8 (q : Pattern) (selected : d9076 q = 2) : d94671 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d9076, d94671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9076, d94671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d9077 q = 2) : d94672 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d9077, d94672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9077, d94672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d9078 q = 2) : d94673 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d9078, d94673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9078, d94673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d9244 q = 2) : d94704 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d9244, d94704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9244, d94704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8821 q selected
  have h12 (q : Pattern) (selected : d9245 q = 2) : d94705 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d9245, d94705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9245, d94705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d9246 q = 2) : d94706 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d9246, d94706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9246, d94706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d9247 q = 2) : d94707 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d9247, d94707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9247, d94707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d9248 q = 2) : d94708 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d9248, d94708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d9248, d94708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d9249 q = 2) : d94709 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d9249, d94709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d9249, d94709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro8823 (p : Pattern) (selected : d9255 p = 2) : d94715 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d9250 q = 2) : d94710 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d9250, d94710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8822 q selected
    | true =>
      simp only [d9250, d94710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9251 q = 2) : d94711 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d9251, d94711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9251, d94711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d9252 q = 2) : d94712 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d9252, d94712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9252, d94712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9253 q = 2) : d94713 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d9253, d94713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9253, d94713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9254 q = 2) : d94714 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d9254, d94714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9254, d94714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9255 q = 2) : d94715 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d9255, d94715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9255, d94715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8824 (p : Pattern) (selected : d9261 p = 2) : d94721 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d9256 q = 2) : d94716 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d9256, d94716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8823 q selected
    | true =>
      simp only [d9256, d94716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9257 q = 2) : d94717 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d9257, d94717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9257, d94717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d9258 q = 2) : d94718 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d9258, d94718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9258, d94718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9259 q = 2) : d94719 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d9259, d94719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9259, d94719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9260 q = 2) : d94720 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d9260, d94720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9260, d94720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9261 q = 2) : d94721 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d9261, d94721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9261, d94721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8825 (p : Pattern) (selected : d9267 p = 2) : d94727 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d9262 q = 2) : d94722 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d9262, d94722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8824 q selected
    | true =>
      simp only [d9262, d94722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9263 q = 2) : d94723 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d9263, d94723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9263, d94723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d9264 q = 2) : d94724 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d9264, d94724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9264, d94724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9265 q = 2) : d94725 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d9265, d94725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9265, d94725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9266 q = 2) : d94726 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d9266, d94726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9266, d94726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9267 q = 2) : d94727 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d9267, d94727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9267, d94727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8826 (p : Pattern) (selected : d9273 p = 2) : d94733 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d9268 q = 2) : d94728 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d9268, d94728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8825 q selected
    | true =>
      simp only [d9268, d94728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9269 q = 2) : d94729 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d9269, d94729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9269, d94729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d9270 q = 2) : d94730 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d9270, d94730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9270, d94730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9271 q = 2) : d94731 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d9271, d94731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9271, d94731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9272 q = 2) : d94732 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d9272, d94732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9272, d94732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9273 q = 2) : d94733 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d9273, d94733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9273, d94733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8827 (p : Pattern) (selected : d9279 p = 2) : d94739 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d9274 q = 2) : d94734 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d9274, d94734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8826 q selected
    | true =>
      simp only [d9274, d94734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9275 q = 2) : d94735 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d9275, d94735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9275, d94735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d9276 q = 2) : d94736 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d9276, d94736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9276, d94736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9277 q = 2) : d94737 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d9277, d94737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9277, d94737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9278 q = 2) : d94738 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d9278, d94738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9278, d94738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9279 q = 2) : d94739 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d9279, d94739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9279, d94739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8828 (p : Pattern) (selected : d9285 p = 2) : d94745 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d9280 q = 2) : d94740 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d9280, d94740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8827 q selected
    | true =>
      simp only [d9280, d94740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9281 q = 2) : d94741 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d9281, d94741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9281, d94741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d9282 q = 2) : d94742 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d9282, d94742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9282, d94742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9283 q = 2) : d94743 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d9283, d94743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9283, d94743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9284 q = 2) : d94744 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d9284, d94744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9284, d94744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9285 q = 2) : d94745 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d9285, d94745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9285, d94745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8829 (p : Pattern) (selected : d9291 p = 2) : d94751 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d9286 q = 2) : d94746 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d9286, d94746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8828 q selected
    | true =>
      simp only [d9286, d94746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9287 q = 2) : d94747 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d9287, d94747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9287, d94747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d9288 q = 2) : d94748 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d9288, d94748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9288, d94748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9289 q = 2) : d94749 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d9289, d94749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9289, d94749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9290 q = 2) : d94750 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d9290, d94750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9290, d94750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9291 q = 2) : d94751 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d9291, d94751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9291, d94751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8830 (p : Pattern) (selected : d23 p = 0) : d51875 p = 1 := by
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
  have h4 (q : Pattern) (selected : d22 q = 0) : d51874 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d22, d51874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d22, d51874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d23 q = 0) : d51875 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23, d51875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d23, d51875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro8831 (p : Pattern) (selected : d116758 p = 0) : d118619 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116754 q = 0) : d118615 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116754, d118615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8830 q selected
    | true =>
      simp only [d116754, d118615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116755 q = 0) : d118616 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116755, d118616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d116755, d118616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d116756 q = 0) : d118617 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d116756, d118617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116756, d118617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116757 q = 0) : d118618 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d116757, d118618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116757, d118618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116758 q = 0) : d118619 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d116758, d118619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d116758, d118619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro8832 (p : Pattern) (selected : d116764 p = 0) : d118625 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116759 q = 0) : d118620 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d116759, d118620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8831 q selected
    | true =>
      simp only [d116759, d118620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116760 q = 0) : d118621 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d116760, d118621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116760, d118621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116761 q = 0) : d118622 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d116761, d118622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116761, d118622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116762 q = 0) : d118623 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d116762, d118623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116762, d118623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116763 q = 0) : d118624 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d116763, d118624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d116763, d118624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d116764 q = 0) : d118625 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d116764, d118625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116764, d118625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8833 (p : Pattern) (selected : d116770 p = 0) : d118631 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116765 q = 0) : d118626 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116765, d118626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8832 q selected
    | true =>
      simp only [d116765, d118626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116766 q = 0) : d118627 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116766, d118627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116766, d118627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116767 q = 0) : d118628 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d116767, d118628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116767, d118628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116768 q = 0) : d118629 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d116768, d118629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116768, d118629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116769 q = 0) : d118630 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d116769, d118630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d116769, d118630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d116770 q = 0) : d118631 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d116770, d118631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116770, d118631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro8834 (p : Pattern) (selected : d116776 p = 0) : d118637 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116771 q = 0) : d118632 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116771, d118632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8833 q selected
    | true =>
      simp only [d116771, d118632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116772 q = 0) : d118633 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d116772, d118633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d116772, d118633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d116773 q = 0) : d118634 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d116773, d118634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116773, d118634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116774 q = 0) : d118635 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d116774, d118635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116774, d118635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d116775 q = 0) : d118636 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d116775, d118636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116775, d118636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116776 q = 0) : d118637 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d116776, d118637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116776, d118637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro8835 (p : Pattern) (selected : d116777 p = 0) : d118638 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116765 q = 0) : d118626 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116765, d118626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8832 q selected
    | true =>
      simp only [d116765, d118626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116766 q = 0) : d118627 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116766, d118627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116766, d118627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116767 q = 0) : d118628 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d116767, d118628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116767, d118628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116768 q = 0) : d118629 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d116768, d118629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116768, d118629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116769 q = 0) : d118630 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d116769, d118630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d116769, d118630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d116777 q = 0) : d118638 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d116777, d118638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116777, d118638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8836 (p : Pattern) (selected : d116783 p = 0) : d118644 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116771 q = 0) : d118632 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116771, d118632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8833 q selected
    | true =>
      simp only [d116771, d118632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116772 q = 0) : d118633 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d116772, d118633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d116772, d118633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d116773 q = 0) : d118634 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d116773, d118634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116773, d118634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116774 q = 0) : d118635 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d116774, d118635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116774, d118635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d116775 q = 0) : d118636 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d116775, d118636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116775, d118636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116778 q = 0) : d118639 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116778, d118639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8835 q selected
    | true =>
      simp only [d116778, d118639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d116779 q = 0) : d118640 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d116779, d118640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d116779, d118640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d116780 q = 0) : d118641 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d116780, d118641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d116780, d118641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d116781 q = 0) : d118642 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d116781, d118642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116781, d118642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d116782 q = 0) : d118643 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d116782, d118643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116782, d118643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d116783 q = 0) : d118644 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d116783, d118644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116783, d118644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro8837 (p : Pattern) (selected : d116788 p = 0) : d118649 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116778 q = 0) : d118639 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116778, d118639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8835 q selected
    | true =>
      simp only [d116778, d118639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116779 q = 0) : d118640 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d116779, d118640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d116779, d118640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d116780 q = 0) : d118641 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d116780, d118641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116780, d118641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116781 q = 0) : d118642 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d116781, d118642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116781, d118642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d116782 q = 0) : d118643 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d116782, d118643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116782, d118643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116788 q = 0) : d118649 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d116788, d118649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116788, d118649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro8838 (p : Pattern) (selected : d116798 p = 0) : d118659 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116794 q = 0) : d118655 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116794, d118655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116794, d118655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8830 q selected
  have h2 (q : Pattern) (selected : d116754 q = 0) : d118615 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116754, d118615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8830 q selected
    | true =>
      simp only [d116754, d118615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d116795 q = 0) : d118656 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116795, d118656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d116795, d118656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116755 q = 0) : d118616 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116755, d118616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116755, d118616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116796 q = 0) : d118657 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d116796, d118657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116796, d118657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116797 q = 0) : d118658 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d116797, d118658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116797, d118658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d116798 q = 0) : d118659 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d116798, d118659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d116798, d118659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro8839 (p : Pattern) (selected : d116804 p = 0) : d118665 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116799 q = 0) : d118660 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d116799, d118660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8838 q selected
    | true =>
      simp only [d116799, d118660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116800 q = 0) : d118661 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d116800, d118661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116800, d118661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116801 q = 0) : d118662 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d116801, d118662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116801, d118662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116802 q = 0) : d118663 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d116802, d118663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116802, d118663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116803 q = 0) : d118664 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d116803, d118664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d116803, d118664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d116804 q = 0) : d118665 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d116804, d118665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116804, d118665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8840 (p : Pattern) (selected : d116810 p = 0) : d118671 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116805 q = 0) : d118666 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116805, d118666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8839 q selected
    | true =>
      simp only [d116805, d118666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116806 q = 0) : d118667 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116806, d118667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116806, d118667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116807 q = 0) : d118668 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d116807, d118668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116807, d118668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116808 q = 0) : d118669 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d116808, d118669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116808, d118669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116809 q = 0) : d118670 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d116809, d118670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d116809, d118670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d116810 q = 0) : d118671 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d116810, d118671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116810, d118671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8841 (p : Pattern) (selected : d116816 p = 0) : d118677 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116811 q = 0) : d118672 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116811, d118672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8840 q selected
    | true =>
      simp only [d116811, d118672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116812 q = 0) : d118673 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d116812, d118673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d116812, d118673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d116813 q = 0) : d118674 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d116813, d118674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116813, d118674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116814 q = 0) : d118675 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d116814, d118675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116814, d118675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d116815 q = 0) : d118676 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d116815, d118676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116815, d118676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116816 q = 0) : d118677 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d116816, d118677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116816, d118677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro8842 (p : Pattern) (selected : d116822 p = 0) : d118683 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116784 q = 0) : d118645 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d116784, d118645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8834 q selected
    | true =>
      simp only [d116784, d118645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8836 q selected
  have h2 (q : Pattern) (selected : d116785 q = 0) : d118646 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d116785, d118646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d116785, d118646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d116786 q = 0) : d118647 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d116786, d118647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116786, d118647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116787 q = 0) : d118648 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d116787, d118648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116787, d118648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d116789 q = 0) : d118650 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d116789, d118650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116789, d118650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8837 q selected
  have h6 (q : Pattern) (selected : d116790 q = 0) : d118651 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d116790, d118651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116790, d118651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d116791 q = 0) : d118652 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d116791, d118652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d116791, d118652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d116792 q = 0) : d118653 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d116792, d118653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d116792, d118653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d116793 q = 0) : d118654 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d116793, d118654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d116793, d118654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d116817 q = 0) : d118678 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d116817, d118678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116817, d118678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8841 q selected
  have h11 (q : Pattern) (selected : d116818 q = 0) : d118679 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d116818, d118679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d116818, d118679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d116819 q = 0) : d118680 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d116819, d118680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d116819, d118680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d116820 q = 0) : d118681 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d116820, d118681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d116820, d118681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d116821 q = 0) : d118682 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d116821, d118682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d116821, d118682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d116822 q = 0) : d118683 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d116822, d118683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d116822, d118683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro8843 (p : Pattern) (selected : d116832 p = 0) : d118693 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116771 q = 0) : d118632 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116771, d118632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8833 q selected
    | true =>
      simp only [d116771, d118632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116828 q = 0) : d118689 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d116828, d118689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116828, d118689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116829 q = 0) : d118690 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d116829, d118690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116829, d118690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116830 q = 0) : d118691 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d116830, d118691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116830, d118691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d116831 q = 0) : d118692 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d116831, d118692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116831, d118692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116832 q = 0) : d118693 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d116832, d118693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116832, d118693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro8844 (p : Pattern) (selected : d116839 p = 0) : d118700 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116771 q = 0) : d118632 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116771, d118632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8833 q selected
    | true =>
      simp only [d116771, d118632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116828 q = 0) : d118689 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d116828, d118689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116828, d118689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116829 q = 0) : d118690 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d116829, d118690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116829, d118690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116830 q = 0) : d118691 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d116830, d118691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116830, d118691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d116831 q = 0) : d118692 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d116831, d118692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116831, d118692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116778 q = 0) : d118639 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116778, d118639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8835 q selected
    | true =>
      simp only [d116778, d118639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d116835 q = 0) : d118696 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d116835, d118696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116835, d118696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d116836 q = 0) : d118697 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d116836, d118697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d116836, d118697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d116837 q = 0) : d118698 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d116837, d118698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116837, d118698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d116838 q = 0) : d118699 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d116838, d118699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116838, d118699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d116839 q = 0) : d118700 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d116839, d118700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116839, d118700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro8845 (p : Pattern) (selected : d116844 p = 0) : d118705 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116765 q = 0) : d118626 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116765, d118626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8832 q selected
    | true =>
      simp only [d116765, d118626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116766 q = 0) : d118627 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116766, d118627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116766, d118627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116767 q = 0) : d118628 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d116767, d118628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116767, d118628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116768 q = 0) : d118629 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d116768, d118629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116768, d118629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116843 q = 0) : d118704 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d116843, d118704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116843, d118704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116844 q = 0) : d118705 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d116844, d118705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116844, d118705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro8846 (p : Pattern) (selected : d116851 p = 0) : d118712 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116765 q = 0) : d118626 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116765, d118626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8832 q selected
    | true =>
      simp only [d116765, d118626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116766 q = 0) : d118627 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116766, d118627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116766, d118627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116767 q = 0) : d118628 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d116767, d118628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116767, d118628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116849 q = 0) : d118710 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d116849, d118710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116849, d118710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d116850 q = 0) : d118711 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d116850, d118711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d116850, d118711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d116851 q = 0) : d118712 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d116851, d118712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116851, d118712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro8847 (p : Pattern) (selected : d137 p = 0) : d51988 p = 1 := by
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
  have h6 (q : Pattern) (selected : d21 q = 0) : d51873 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136 q = 0) : d51987 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d136, d51987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136, d51987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d137 q = 0) : d51988 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d137, d51988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d137, d51988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8848 (p : Pattern) (selected : d116859 p = 0) : d118720 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116855 q = 0) : d118716 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116855, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8847 q selected
    | true =>
      simp only [d116855, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116856 q = 0) : d118717 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116856, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d116856, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d116857 q = 0) : d118718 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d116857, d118718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116857, d118718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116858 q = 0) : d118719 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d116858, d118719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116858, d118719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116754 q = 0) : d118615 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116754, d118615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8830 q selected
    | true =>
      simp only [d116754, d118615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d116755 q = 0) : d118616 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116755, d118616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116755, d118616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d116756 q = 0) : d118617 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d116756, d118617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116756, d118617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d116757 q = 0) : d118618 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d116757, d118618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d116757, d118618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d116859 q = 0) : d118720 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d116859, d118720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d116859, d118720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro8849 (p : Pattern) (selected : d116865 p = 0) : d118726 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116860 q = 0) : d118721 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d116860, d118721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8848 q selected
    | true =>
      simp only [d116860, d118721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8831 q selected
  have h2 (q : Pattern) (selected : d116861 q = 0) : d118722 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d116861, d118722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116861, d118722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116862 q = 0) : d118723 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d116862, d118723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116862, d118723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116759 q = 0) : d118620 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d116759, d118620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8831 q selected
    | true =>
      simp only [d116759, d118620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116760 q = 0) : d118621 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d116760, d118621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116760, d118621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116761 q = 0) : d118622 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d116761, d118622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116761, d118622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d116863 q = 0) : d118724 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d116863, d118724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116863, d118724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d116762 q = 0) : d118623 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d116762, d118623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d116762, d118623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d116864 q = 0) : d118725 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d116864, d118725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d116864, d118725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d116865 q = 0) : d118726 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d116865, d118726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d116865, d118726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro8850 (p : Pattern) (selected : d116871 p = 0) : d118732 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116866 q = 0) : d118727 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116866, d118727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8849 q selected
    | true =>
      simp only [d116866, d118727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116867 q = 0) : d118728 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116867, d118728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116867, d118728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116765 q = 0) : d118626 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116765, d118626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8832 q selected
    | true =>
      simp only [d116765, d118626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116766 q = 0) : d118627 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116766, d118627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116766, d118627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d116868 q = 0) : d118729 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d116868, d118729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116868, d118729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116869 q = 0) : d118730 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d116869, d118730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116869, d118730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d116870 q = 0) : d118731 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d116870, d118731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d116870, d118731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d116871 q = 0) : d118732 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d116871, d118732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116871, d118732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro8851 (p : Pattern) (selected : d168 p = 0) : d51875 p = 1 := by
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
  have h4 (q : Pattern) (selected : d167 q = 0) : d51874 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d167, d51874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d167, d51874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d168 q = 0) : d51875 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d168, d51875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d168, d51875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro8852 (p : Pattern) (selected : d116877 p = 0) : d118619 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116873 q = 0) : d118615 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116873, d118615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8851 q selected
    | true =>
      simp only [d116873, d118615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116874 q = 0) : d118616 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116874, d118616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d116874, d118616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d116875 q = 0) : d118617 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d116875, d118617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116875, d118617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116876 q = 0) : d118618 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d116876, d118618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116876, d118618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116877 q = 0) : d118619 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d116877, d118619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d116877, d118619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro8853 (p : Pattern) (selected : d116883 p = 0) : d118625 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116878 q = 0) : d118620 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d116878, d118620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8852 q selected
    | true =>
      simp only [d116878, d118620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116879 q = 0) : d118621 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d116879, d118621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116879, d118621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116880 q = 0) : d118622 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d116880, d118622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116880, d118622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116881 q = 0) : d118623 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d116881, d118623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116881, d118623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116882 q = 0) : d118624 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d116882, d118624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d116882, d118624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d116883 q = 0) : d118625 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d116883, d118625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116883, d118625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8854 (p : Pattern) (selected : d116889 p = 0) : d118631 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116884 q = 0) : d118626 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116884, d118626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8853 q selected
    | true =>
      simp only [d116884, d118626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116885 q = 0) : d118627 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116885, d118627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116885, d118627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116886 q = 0) : d118628 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d116886, d118628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116886, d118628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116887 q = 0) : d118629 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d116887, d118629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116887, d118629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116888 q = 0) : d118630 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d116888, d118630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d116888, d118630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d116889 q = 0) : d118631 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d116889, d118631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116889, d118631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro8855 (p : Pattern) (selected : d116895 p = 0) : d118738 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116845 q = 0) : d118706 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116845, d118706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8845 q selected
    | true =>
      simp only [d116845, d118706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116846 q = 0) : d118707 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d116846, d118707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116846, d118707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116847 q = 0) : d118708 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d116847, d118708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116847, d118708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116848 q = 0) : d118709 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d116848, d118709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116848, d118709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d116852 q = 0) : d118713 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116852, d118713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8846 q selected
    | true =>
      simp only [d116852, d118713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d116853 q = 0) : d118714 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d116853, d118714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116853, d118714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d116854 q = 0) : d118715 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d116854, d118715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d116854, d118715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d116872 q = 0) : d118733 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116872, d118733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8850 q selected
    | true =>
      simp only [d116872, d118733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8833 q selected
  have h9 (q : Pattern) (selected : d116890 q = 0) : d118632 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116890, d118632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8854 q selected
    | true =>
      simp only [d116890, d118632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d116891 q = 0) : d118734 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d116891, d118734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d116891, d118734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d116771 q = 0) : d118632 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116771, d118632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8833 q selected
    | true =>
      simp only [d116771, d118632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d116772 q = 0) : d118633 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d116772, d118633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d116772, d118633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d116892 q = 0) : d118735 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d116892, d118735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d116892, d118735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d116893 q = 0) : d118736 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d116893, d118736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d116893, d118736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d116894 q = 0) : d118737 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d116894, d118737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d116894, d118737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d116895 q = 0) : d118738 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d116895, d118738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116895, d118738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro8856 (p : Pattern) (selected : d116896 p = 0) : d118739 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116765 q = 0) : d118626 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116765, d118626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8832 q selected
    | true =>
      simp only [d116765, d118626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116766 q = 0) : d118627 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116766, d118627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116766, d118627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116767 q = 0) : d118628 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d116767, d118628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116767, d118628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116768 q = 0) : d118629 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d116768, d118629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116768, d118629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116843 q = 0) : d118704 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d116843, d118704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116843, d118704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116896 q = 0) : d118739 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d116896, d118739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116896, d118739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8857 (p : Pattern) (selected : d116901 p = 0) : d118744 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116765 q = 0) : d118626 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116765, d118626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8832 q selected
    | true =>
      simp only [d116765, d118626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116766 q = 0) : d118627 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116766, d118627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116766, d118627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116767 q = 0) : d118628 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d116767, d118628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116767, d118628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116849 q = 0) : d118710 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d116849, d118710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116849, d118710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d116850 q = 0) : d118711 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d116850, d118711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d116850, d118711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d116901 q = 0) : d118744 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d116901, d118744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116901, d118744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8858 (p : Pattern) (selected : d116905 p = 0) : d118748 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116866 q = 0) : d118727 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116866, d118727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8849 q selected
    | true =>
      simp only [d116866, d118727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116867 q = 0) : d118728 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116867, d118728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116867, d118728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116765 q = 0) : d118626 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116765, d118626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8832 q selected
    | true =>
      simp only [d116765, d118626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116766 q = 0) : d118627 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116766, d118627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116766, d118627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d116868 q = 0) : d118729 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d116868, d118729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116868, d118729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116869 q = 0) : d118730 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d116869, d118730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116869, d118730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d116870 q = 0) : d118731 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d116870, d118731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d116870, d118731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d116905 q = 0) : d118748 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d116905, d118748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d116905, d118748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8859 (p : Pattern) (selected : d116907 p = 0) : d118638 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116884 q = 0) : d118626 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116884, d118626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8853 q selected
    | true =>
      simp only [d116884, d118626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116885 q = 0) : d118627 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116885, d118627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116885, d118627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116886 q = 0) : d118628 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d116886, d118628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116886, d118628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116887 q = 0) : d118629 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d116887, d118629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116887, d118629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116888 q = 0) : d118630 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d116888, d118630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d116888, d118630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d116907 q = 0) : d118638 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d116907, d118638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116907, d118638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8860 (p : Pattern) (selected : d116913 p = 0) : d118754 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116845 q = 0) : d118706 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116845, d118706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8845 q selected
    | true =>
      simp only [d116845, d118706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116846 q = 0) : d118707 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d116846, d118707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116846, d118707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116847 q = 0) : d118708 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d116847, d118708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116847, d118708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116848 q = 0) : d118709 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d116848, d118709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116848, d118709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d116852 q = 0) : d118713 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116852, d118713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8846 q selected
    | true =>
      simp only [d116852, d118713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d116853 q = 0) : d118714 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d116853, d118714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116853, d118714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d116854 q = 0) : d118715 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d116854, d118715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d116854, d118715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d116872 q = 0) : d118733 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116872, d118733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8850 q selected
    | true =>
      simp only [d116872, d118733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8833 q selected
  have h9 (q : Pattern) (selected : d116890 q = 0) : d118632 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116890, d118632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8854 q selected
    | true =>
      simp only [d116890, d118632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d116891 q = 0) : d118734 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d116891, d118734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d116891, d118734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d116771 q = 0) : d118632 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116771, d118632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8833 q selected
    | true =>
      simp only [d116771, d118632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d116772 q = 0) : d118633 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d116772, d118633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d116772, d118633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d116892 q = 0) : d118735 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d116892, d118735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d116892, d118735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d116893 q = 0) : d118736 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d116893, d118736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d116893, d118736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d116894 q = 0) : d118737 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d116894, d118737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d116894, d118737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d116897 q = 0) : d118740 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116897, d118740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8856 q selected
    | true =>
      simp only [d116897, d118740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d116898 q = 0) : d118741 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d116898, d118741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116898, d118741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d116899 q = 0) : d118742 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d116899, d118742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d116899, d118742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d116900 q = 0) : d118743 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d116900, d118743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116900, d118743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d116902 q = 0) : d118745 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116902, d118745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8857 q selected
    | true =>
      simp only [d116902, d118745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d116903 q = 0) : d118746 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d116903, d118746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116903, d118746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d116904 q = 0) : d118747 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d116904, d118747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d116904, d118747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d116906 q = 0) : d118749 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116906, d118749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8858 q selected
    | true =>
      simp only [d116906, d118749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8835 q selected
  have h24 (q : Pattern) (selected : d116908 q = 0) : d118639 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116908, d118639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8859 q selected
    | true =>
      simp only [d116908, d118639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d116909 q = 0) : d118750 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d116909, d118750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d116909, d118750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d116778 q = 0) : d118639 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116778, d118639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8835 q selected
    | true =>
      simp only [d116778, d118639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d116779 q = 0) : d118640 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d116779, d118640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d116779, d118640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d116910 q = 0) : d118751 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d116910, d118751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d116910, d118751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d116911 q = 0) : d118752 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d116911, d118752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d116911, d118752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d116912 q = 0) : d118753 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d116912, d118753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d116912, d118753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d116913 q = 0) : d118754 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d116913, d118754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d116913, d118754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro8861 (p : Pattern) (selected : d116915 p = 0) : d118756 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116771 q = 0) : d118632 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116771, d118632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8833 q selected
    | true =>
      simp only [d116771, d118632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116828 q = 0) : d118689 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d116828, d118689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116828, d118689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116829 q = 0) : d118690 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d116829, d118690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116829, d118690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116830 q = 0) : d118691 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d116830, d118691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116830, d118691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d116831 q = 0) : d118692 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d116831, d118692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116831, d118692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116915 q = 0) : d118756 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d116915, d118756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116915, d118756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8862 (p : Pattern) (selected : d116922 p = 0) : d118763 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116906 q = 0) : d118749 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116906, d118749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8858 q selected
    | true =>
      simp only [d116906, d118749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8835 q selected
  have h2 (q : Pattern) (selected : d116908 q = 0) : d118639 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116908, d118639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8859 q selected
    | true =>
      simp only [d116908, d118639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d116909 q = 0) : d118750 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d116909, d118750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d116909, d118750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116778 q = 0) : d118639 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116778, d118639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8835 q selected
    | true =>
      simp only [d116778, d118639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116779 q = 0) : d118640 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d116779, d118640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d116779, d118640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d116910 q = 0) : d118751 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d116910, d118751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116910, d118751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d116920 q = 0) : d118761 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d116920, d118761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116920, d118761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d116921 q = 0) : d118762 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d116921, d118762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116921, d118762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d116922 q = 0) : d118763 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d116922, d118763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116922, d118763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro8863 (p : Pattern) (selected : d116932 p = 0) : d118773 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116928 q = 0) : d118769 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116928, d118769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116928, d118769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8847 q selected
  have h2 (q : Pattern) (selected : d116855 q = 0) : d118716 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116855, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8847 q selected
    | true =>
      simp only [d116855, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d116929 q = 0) : d118770 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116929, d118770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d116929, d118770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116856 q = 0) : d118717 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116856, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116856, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116930 q = 0) : d118771 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d116930, d118771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116930, d118771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116931 q = 0) : d118772 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d116931, d118772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116931, d118772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d116794 q = 0) : d118655 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116794, d118655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116794, d118655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8830 q selected
  have h8 (q : Pattern) (selected : d116754 q = 0) : d118615 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116754, d118615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8830 q selected
    | true =>
      simp only [d116754, d118615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d116795 q = 0) : d118656 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116795, d118656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d116795, d118656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d116755 q = 0) : d118616 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116755, d118616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d116755, d118616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d116796 q = 0) : d118657 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d116796, d118657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d116796, d118657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d116797 q = 0) : d118658 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d116797, d118658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d116797, d118658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d116932 q = 0) : d118773 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d116932, d118773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d116932, d118773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro8864 (p : Pattern) (selected : d116938 p = 0) : d118779 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116933 q = 0) : d118774 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d116933, d118774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8863 q selected
    | true =>
      simp only [d116933, d118774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8838 q selected
  have h2 (q : Pattern) (selected : d116934 q = 0) : d118775 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d116934, d118775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116934, d118775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116935 q = 0) : d118776 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d116935, d118776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116935, d118776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116799 q = 0) : d118660 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d116799, d118660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8838 q selected
    | true =>
      simp only [d116799, d118660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116800 q = 0) : d118661 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d116800, d118661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116800, d118661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116801 q = 0) : d118662 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d116801, d118662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116801, d118662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d116936 q = 0) : d118777 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d116936, d118777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116936, d118777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d116802 q = 0) : d118663 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d116802, d118663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d116802, d118663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d116937 q = 0) : d118778 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d116937, d118778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d116937, d118778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d116938 q = 0) : d118779 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d116938, d118779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d116938, d118779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro8865 (p : Pattern) (selected : d116944 p = 0) : d118785 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116939 q = 0) : d118780 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116939, d118780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8864 q selected
    | true =>
      simp only [d116939, d118780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116940 q = 0) : d118781 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116940, d118781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116940, d118781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116805 q = 0) : d118666 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116805, d118666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8839 q selected
    | true =>
      simp only [d116805, d118666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116806 q = 0) : d118667 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116806, d118667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116806, d118667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d116941 q = 0) : d118782 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d116941, d118782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116941, d118782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116942 q = 0) : d118783 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d116942, d118783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116942, d118783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d116943 q = 0) : d118784 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d116943, d118784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d116943, d118784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d116944 q = 0) : d118785 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d116944, d118785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d116944, d118785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8866 (p : Pattern) (selected : d116950 p = 0) : d118659 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116946 q = 0) : d118655 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116946, d118655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116946, d118655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8851 q selected
  have h2 (q : Pattern) (selected : d116873 q = 0) : d118615 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116873, d118615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8851 q selected
    | true =>
      simp only [d116873, d118615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d116947 q = 0) : d118656 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116947, d118656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d116947, d118656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116874 q = 0) : d118616 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116874, d118616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116874, d118616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116948 q = 0) : d118657 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d116948, d118657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116948, d118657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116949 q = 0) : d118658 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d116949, d118658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116949, d118658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d116950 q = 0) : d118659 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d116950, d118659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d116950, d118659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro8867 (p : Pattern) (selected : d116956 p = 0) : d118665 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116951 q = 0) : d118660 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d116951, d118660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8866 q selected
    | true =>
      simp only [d116951, d118660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116952 q = 0) : d118661 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d116952, d118661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116952, d118661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116953 q = 0) : d118662 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d116953, d118662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116953, d118662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116954 q = 0) : d118663 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d116954, d118663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116954, d118663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116955 q = 0) : d118664 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d116955, d118664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d116955, d118664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d116956 q = 0) : d118665 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d116956, d118665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116956, d118665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8868 (p : Pattern) (selected : d116962 p = 0) : d118671 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116957 q = 0) : d118666 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116957, d118666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8867 q selected
    | true =>
      simp only [d116957, d118666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116958 q = 0) : d118667 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116958, d118667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116958, d118667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116959 q = 0) : d118668 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d116959, d118668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116959, d118668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116960 q = 0) : d118669 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d116960, d118669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116960, d118669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116961 q = 0) : d118670 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d116961, d118670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d116961, d118670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d116962 q = 0) : d118671 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d116962, d118671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116962, d118671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8869 (p : Pattern) (selected : d116968 p = 0) : d118791 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116945 q = 0) : d118786 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116945, d118786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8865 q selected
    | true =>
      simp only [d116945, d118786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8840 q selected
  have h2 (q : Pattern) (selected : d116963 q = 0) : d118672 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116963, d118672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8868 q selected
    | true =>
      simp only [d116963, d118672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d116964 q = 0) : d118787 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d116964, d118787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d116964, d118787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116811 q = 0) : d118672 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116811, d118672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8840 q selected
    | true =>
      simp only [d116811, d118672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116812 q = 0) : d118673 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d116812, d118673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d116812, d118673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d116965 q = 0) : d118788 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d116965, d118788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116965, d118788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d116966 q = 0) : d118789 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d116966, d118789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116966, d118789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d116967 q = 0) : d118790 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d116967, d118790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116967, d118790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d116968 q = 0) : d118791 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d116968, d118791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116968, d118791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro8870 (p : Pattern) (selected : d116974 p = 0) : d118797 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116833 q = 0) : d118694 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d116833, d118694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116833, d118694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8843 q selected
  have h2 (q : Pattern) (selected : d116834 q = 0) : d118695 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d116834, d118695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d116834, d118695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d116840 q = 0) : d118701 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d116840, d118701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8843 q selected
    | true =>
      simp only [d116840, d118701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8844 q selected
  have h4 (q : Pattern) (selected : d116841 q = 0) : d118702 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d116841, d118702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116841, d118702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116842 q = 0) : d118703 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d116842, d118703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116842, d118703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116914 q = 0) : d118755 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d116914, d118755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8855 q selected
    | true =>
      simp only [d116914, d118755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8860 q selected
  have h7 (q : Pattern) (selected : d116916 q = 0) : d118757 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d116916, d118757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8861 q selected
    | true =>
      simp only [d116916, d118757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d116917 q = 0) : d118758 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d116917, d118758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d116917, d118758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d116918 q = 0) : d118759 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d116918, d118759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d116918, d118759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d116919 q = 0) : d118760 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d116919, d118760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116919, d118760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d116923 q = 0) : d118764 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d116923, d118764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116923, d118764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8862 q selected
  have h12 (q : Pattern) (selected : d116924 q = 0) : d118765 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d116924, d118765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d116924, d118765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d116925 q = 0) : d118766 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d116925, d118766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d116925, d118766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d116926 q = 0) : d118767 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d116926, d118767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d116926, d118767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d116927 q = 0) : d118768 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d116927, d118768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d116927, d118768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d116969 q = 0) : d118792 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d116969, d118792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116969, d118792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8869 q selected
  have h17 (q : Pattern) (selected : d116970 q = 0) : d118793 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d116970, d118793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d116970, d118793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d116971 q = 0) : d118794 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d116971, d118794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d116971, d118794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d116972 q = 0) : d118795 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d116972, d118795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d116972, d118795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d116973 q = 0) : d118796 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d116973, d118796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d116973, d118796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d116974 q = 0) : d118797 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d116974, d118797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d116974, d118797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro8871 (p : Pattern) (selected : d116980 p = 0) : d118803 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116823 q = 0) : d118684 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d116823, d118684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116823, d118684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8842 q selected
  have h2 (q : Pattern) (selected : d116824 q = 0) : d118685 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d116824, d118685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116824, d118685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116825 q = 0) : d118686 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d116825, d118686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116825, d118686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116826 q = 0) : d118687 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d116826, d118687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116826, d118687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d116827 q = 0) : d118688 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d116827, d118688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116827, d118688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116975 q = 0) : d118798 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d116975, d118798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116975, d118798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8870 q selected
  have h7 (q : Pattern) (selected : d116976 q = 0) : d118799 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d116976, d118799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116976, d118799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d116977 q = 0) : d118800 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d116977, d118800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116977, d118800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d116978 q = 0) : d118801 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d116978, d118801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116978, d118801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d116979 q = 0) : d118802 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d116979, d118802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116979, d118802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d116980 q = 0) : d118803 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d116980, d118803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116980, d118803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro8872 (p : Pattern) (selected : d116985 p = 0) : d118808 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116872 q = 0) : d118733 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116872, d118733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8850 q selected
    | true =>
      simp only [d116872, d118733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8833 q selected
  have h2 (q : Pattern) (selected : d116981 q = 0) : d118804 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d116981, d118804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116981, d118804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116982 q = 0) : d118805 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d116982, d118805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116982, d118805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116983 q = 0) : d118806 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d116983, d118806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116983, d118806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d116984 q = 0) : d118807 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d116984, d118807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116984, d118807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116985 q = 0) : d118808 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d116985, d118808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116985, d118808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro8873 (p : Pattern) (selected : d116992 p = 0) : d118815 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116872 q = 0) : d118733 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116872, d118733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8850 q selected
    | true =>
      simp only [d116872, d118733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8833 q selected
  have h2 (q : Pattern) (selected : d116981 q = 0) : d118804 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d116981, d118804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116981, d118804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116982 q = 0) : d118805 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d116982, d118805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116982, d118805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116983 q = 0) : d118806 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d116983, d118806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116983, d118806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d116984 q = 0) : d118807 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d116984, d118807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116984, d118807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116906 q = 0) : d118749 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116906, d118749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8858 q selected
    | true =>
      simp only [d116906, d118749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8835 q selected
  have h7 (q : Pattern) (selected : d116988 q = 0) : d118811 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d116988, d118811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116988, d118811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d116989 q = 0) : d118812 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d116989, d118812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d116989, d118812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d116990 q = 0) : d118813 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d116990, d118813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116990, d118813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d116991 q = 0) : d118814 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d116991, d118814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116991, d118814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d116992 q = 0) : d118815 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d116992, d118815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116992, d118815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro8874 (p : Pattern) (selected : d116997 p = 0) : d118820 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116866 q = 0) : d118727 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116866, d118727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8849 q selected
    | true =>
      simp only [d116866, d118727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116867 q = 0) : d118728 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116867, d118728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116867, d118728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116765 q = 0) : d118626 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116765, d118626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8832 q selected
    | true =>
      simp only [d116765, d118626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116766 q = 0) : d118627 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116766, d118627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116766, d118627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d116868 q = 0) : d118729 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d116868, d118729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116868, d118729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116869 q = 0) : d118730 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d116869, d118730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116869, d118730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d116996 q = 0) : d118819 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d116996, d118819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116996, d118819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d116997 q = 0) : d118820 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d116997, d118820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116997, d118820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro8875 (p : Pattern) (selected : d117004 p = 0) : d118827 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116866 q = 0) : d118727 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116866, d118727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8849 q selected
    | true =>
      simp only [d116866, d118727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116867 q = 0) : d118728 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116867, d118728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116867, d118728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116765 q = 0) : d118626 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116765, d118626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8832 q selected
    | true =>
      simp only [d116765, d118626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116766 q = 0) : d118627 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116766, d118627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116766, d118627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d116868 q = 0) : d118729 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d116868, d118729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116868, d118729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117002 q = 0) : d118825 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117002, d118825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117002, d118825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117003 q = 0) : d118826 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117003, d118826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117003, d118826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117004 q = 0) : d118827 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117004, d118827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117004, d118827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro8876 (p : Pattern) (selected : d317 p = 0) : d52116 p = 1 := by
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
  have h5 (q : Pattern) (selected : d315 q = 0) : d52114 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d52114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d315, d52114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
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
  have h8 (q : Pattern) (selected : d135 q = 0) : d51986 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d51986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135, d51986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d316 q = 0) : d52115 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d316, d52115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d316, d52115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d317 q = 0) : d52116 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d317, d52116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d317, d52116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro8877 (p : Pattern) (selected : d117012 p = 0) : d118835 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117008 q = 0) : d118831 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117008, d118831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8876 q selected
    | true =>
      simp only [d117008, d118831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117009 q = 0) : d118832 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117009, d118832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117009, d118832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117010 q = 0) : d118833 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117010, d118833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117010, d118833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117011 q = 0) : d118834 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117011, d118834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117011, d118834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116855 q = 0) : d118716 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116855, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8847 q selected
    | true =>
      simp only [d116855, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d116856 q = 0) : d118717 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116856, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116856, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d116857 q = 0) : d118718 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d116857, d118718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116857, d118718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d116858 q = 0) : d118719 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d116858, d118719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d116858, d118719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117012 q = 0) : d118835 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117012, d118835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117012, d118835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro8878 (p : Pattern) (selected : d117018 p = 0) : d118841 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117013 q = 0) : d118836 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117013, d118836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8877 q selected
    | true =>
      simp only [d117013, d118836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8848 q selected
  have h2 (q : Pattern) (selected : d117014 q = 0) : d118837 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117014, d118837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117014, d118837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117015 q = 0) : d118838 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117015, d118838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117015, d118838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116860 q = 0) : d118721 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d116860, d118721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8848 q selected
    | true =>
      simp only [d116860, d118721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8831 q selected
  have h5 (q : Pattern) (selected : d116861 q = 0) : d118722 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d116861, d118722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116861, d118722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116862 q = 0) : d118723 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d116862, d118723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116862, d118723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117016 q = 0) : d118839 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117016, d118839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117016, d118839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d116759 q = 0) : d118620 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d116759, d118620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8831 q selected
    | true =>
      simp only [d116759, d118620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d116760 q = 0) : d118621 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d116760, d118621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116760, d118621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d116761 q = 0) : d118622 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d116761, d118622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116761, d118622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d116863 q = 0) : d118724 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d116863, d118724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d116863, d118724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d117017 q = 0) : d118840 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117017, d118840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117017, d118840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d117018 q = 0) : d118841 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117018, d118841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d117018, d118841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro8879 (p : Pattern) (selected : d117024 p = 0) : d118847 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117019 q = 0) : d118842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117019, d118842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8878 q selected
    | true =>
      simp only [d117019, d118842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117020 q = 0) : d118843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117020, d118843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117020, d118843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116866 q = 0) : d118727 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116866, d118727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8849 q selected
    | true =>
      simp only [d116866, d118727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116867 q = 0) : d118728 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116867, d118728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116867, d118728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117021 q = 0) : d118844 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117021, d118844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117021, d118844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117022 q = 0) : d118845 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117022, d118845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117022, d118845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117023 q = 0) : d118846 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117023, d118846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117023, d118846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117024 q = 0) : d118847 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117024, d118847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117024, d118847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro8880 (p : Pattern) (selected : d348 p = 0) : d51988 p = 1 := by
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
  have h6 (q : Pattern) (selected : d166 q = 0) : d51873 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d166, d51873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166, d51873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d347 q = 0) : d51987 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d347, d51987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d347, d51987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d348 q = 0) : d51988 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d348, d51988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d348, d51988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8881 (p : Pattern) (selected : d117030 p = 0) : d118720 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117026 q = 0) : d118716 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117026, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8880 q selected
    | true =>
      simp only [d117026, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117027 q = 0) : d118717 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117027, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117027, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117028 q = 0) : d118718 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117028, d118718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117028, d118718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117029 q = 0) : d118719 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117029, d118719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117029, d118719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116873 q = 0) : d118615 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116873, d118615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8851 q selected
    | true =>
      simp only [d116873, d118615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d116874 q = 0) : d118616 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116874, d118616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116874, d118616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d116875 q = 0) : d118617 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d116875, d118617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116875, d118617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d116876 q = 0) : d118618 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d116876, d118618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d116876, d118618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117030 q = 0) : d118720 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117030, d118720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117030, d118720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro8882 (p : Pattern) (selected : d117036 p = 0) : d118726 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117031 q = 0) : d118721 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117031, d118721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8881 q selected
    | true =>
      simp only [d117031, d118721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8852 q selected
  have h2 (q : Pattern) (selected : d117032 q = 0) : d118722 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117032, d118722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117032, d118722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117033 q = 0) : d118723 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117033, d118723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117033, d118723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116878 q = 0) : d118620 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d116878, d118620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8852 q selected
    | true =>
      simp only [d116878, d118620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116879 q = 0) : d118621 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d116879, d118621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116879, d118621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116880 q = 0) : d118622 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d116880, d118622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116880, d118622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117034 q = 0) : d118724 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117034, d118724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117034, d118724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d116881 q = 0) : d118623 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d116881, d118623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d116881, d118623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117035 q = 0) : d118725 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117035, d118725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117035, d118725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117036 q = 0) : d118726 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117036, d118726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117036, d118726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro8883 (p : Pattern) (selected : d117042 p = 0) : d118732 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117037 q = 0) : d118727 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117037, d118727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8882 q selected
    | true =>
      simp only [d117037, d118727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117038 q = 0) : d118728 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117038, d118728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117038, d118728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116884 q = 0) : d118626 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116884, d118626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8853 q selected
    | true =>
      simp only [d116884, d118626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116885 q = 0) : d118627 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116885, d118627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116885, d118627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117039 q = 0) : d118729 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117039, d118729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117039, d118729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117040 q = 0) : d118730 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117040, d118730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117040, d118730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117041 q = 0) : d118731 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117041, d118731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117041, d118731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117042 q = 0) : d118732 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117042, d118732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117042, d118732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro8884 (p : Pattern) (selected : d117048 p = 0) : d118853 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116866 q = 0) : d118727 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116866, d118727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8849 q selected
    | true =>
      simp only [d116866, d118727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116867 q = 0) : d118728 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116867, d118728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116867, d118728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117045 q = 0) : d118850 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117045, d118850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117045, d118850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117046 q = 0) : d118851 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117046, d118851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117046, d118851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117047 q = 0) : d118852 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117047, d118852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117047, d118852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117048 q = 0) : d118853 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117048, d118853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117048, d118853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro8885 (p : Pattern) (selected : d117054 p = 0) : d118859 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116998 q = 0) : d118821 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116998, d118821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8874 q selected
    | true =>
      simp only [d116998, d118821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8845 q selected
  have h2 (q : Pattern) (selected : d116999 q = 0) : d118822 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d116999, d118822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116999, d118822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117000 q = 0) : d118823 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117000, d118823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117000, d118823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117001 q = 0) : d118824 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117001, d118824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117001, d118824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117005 q = 0) : d118828 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117005, d118828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8875 q selected
    | true =>
      simp only [d117005, d118828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8846 q selected
  have h6 (q : Pattern) (selected : d117006 q = 0) : d118829 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117006, d118829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117006, d118829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117007 q = 0) : d118830 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117007, d118830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117007, d118830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117025 q = 0) : d118848 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117025, d118848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8879 q selected
    | true =>
      simp only [d117025, d118848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8850 q selected
  have h9 (q : Pattern) (selected : d117043 q = 0) : d118733 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117043, d118733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8883 q selected
    | true =>
      simp only [d117043, d118733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8854 q selected
  have h10 (q : Pattern) (selected : d117044 q = 0) : d118849 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117044, d118849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117044, d118849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d117049 q = 0) : d118854 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117049, d118854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8884 q selected
    | true =>
      simp only [d117049, d118854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d117050 q = 0) : d118855 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117050, d118855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d117050, d118855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d117051 q = 0) : d118856 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117051, d118856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d117051, d118856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d117052 q = 0) : d118857 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117052, d118857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117052, d118857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d117053 q = 0) : d118858 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117053, d118858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117053, d118858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d117054 q = 0) : d118859 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117054, d118859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117054, d118859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro8886 (p : Pattern) (selected : d117055 p = 0) : d118860 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116866 q = 0) : d118727 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116866, d118727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8849 q selected
    | true =>
      simp only [d116866, d118727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116867 q = 0) : d118728 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116867, d118728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116867, d118728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116765 q = 0) : d118626 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116765, d118626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8832 q selected
    | true =>
      simp only [d116765, d118626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116766 q = 0) : d118627 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116766, d118627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116766, d118627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d116868 q = 0) : d118729 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d116868, d118729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116868, d118729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116869 q = 0) : d118730 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d116869, d118730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116869, d118730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d116996 q = 0) : d118819 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d116996, d118819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116996, d118819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117055 q = 0) : d118860 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117055, d118860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117055, d118860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8887 (p : Pattern) (selected : d117060 p = 0) : d118865 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116866 q = 0) : d118727 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116866, d118727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8849 q selected
    | true =>
      simp only [d116866, d118727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116867 q = 0) : d118728 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116867, d118728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116867, d118728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116765 q = 0) : d118626 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116765, d118626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8832 q selected
    | true =>
      simp only [d116765, d118626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116766 q = 0) : d118627 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116766, d118627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116766, d118627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d116868 q = 0) : d118729 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d116868, d118729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116868, d118729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117002 q = 0) : d118825 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117002, d118825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117002, d118825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117003 q = 0) : d118826 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117003, d118826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117003, d118826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117060 q = 0) : d118865 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117060, d118865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117060, d118865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8888 (p : Pattern) (selected : d117064 p = 0) : d118869 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117019 q = 0) : d118842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117019, d118842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8878 q selected
    | true =>
      simp only [d117019, d118842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117020 q = 0) : d118843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117020, d118843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117020, d118843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116866 q = 0) : d118727 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116866, d118727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8849 q selected
    | true =>
      simp only [d116866, d118727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116867 q = 0) : d118728 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116867, d118728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116867, d118728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117021 q = 0) : d118844 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117021, d118844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117021, d118844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117022 q = 0) : d118845 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117022, d118845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117022, d118845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117023 q = 0) : d118846 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117023, d118846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117023, d118846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117064 q = 0) : d118869 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117064, d118869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117064, d118869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8889 (p : Pattern) (selected : d117066 p = 0) : d118748 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117037 q = 0) : d118727 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117037, d118727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8882 q selected
    | true =>
      simp only [d117037, d118727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117038 q = 0) : d118728 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117038, d118728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117038, d118728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116884 q = 0) : d118626 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116884, d118626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8853 q selected
    | true =>
      simp only [d116884, d118626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116885 q = 0) : d118627 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116885, d118627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116885, d118627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117039 q = 0) : d118729 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117039, d118729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117039, d118729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117040 q = 0) : d118730 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117040, d118730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117040, d118730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117041 q = 0) : d118731 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117041, d118731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117041, d118731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117066 q = 0) : d118748 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117066, d118748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117066, d118748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8890 (p : Pattern) (selected : d117069 p = 0) : d118872 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116866 q = 0) : d118727 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116866, d118727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8849 q selected
    | true =>
      simp only [d116866, d118727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116867 q = 0) : d118728 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116867, d118728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116867, d118728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117045 q = 0) : d118850 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117045, d118850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117045, d118850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117046 q = 0) : d118851 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117046, d118851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117046, d118851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117047 q = 0) : d118852 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117047, d118852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117047, d118852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117069 q = 0) : d118872 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117069, d118872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117069, d118872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8891 (p : Pattern) (selected : d117075 p = 0) : d118878 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116998 q = 0) : d118821 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116998, d118821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8874 q selected
    | true =>
      simp only [d116998, d118821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8845 q selected
  have h2 (q : Pattern) (selected : d116999 q = 0) : d118822 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d116999, d118822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116999, d118822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117000 q = 0) : d118823 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117000, d118823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117000, d118823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117001 q = 0) : d118824 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117001, d118824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117001, d118824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117005 q = 0) : d118828 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117005, d118828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8875 q selected
    | true =>
      simp only [d117005, d118828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8846 q selected
  have h6 (q : Pattern) (selected : d117006 q = 0) : d118829 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117006, d118829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117006, d118829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117007 q = 0) : d118830 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117007, d118830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117007, d118830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117025 q = 0) : d118848 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117025, d118848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8879 q selected
    | true =>
      simp only [d117025, d118848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8850 q selected
  have h9 (q : Pattern) (selected : d117043 q = 0) : d118733 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117043, d118733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8883 q selected
    | true =>
      simp only [d117043, d118733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8854 q selected
  have h10 (q : Pattern) (selected : d117044 q = 0) : d118849 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117044, d118849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117044, d118849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d117049 q = 0) : d118854 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117049, d118854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8884 q selected
    | true =>
      simp only [d117049, d118854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d117050 q = 0) : d118855 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117050, d118855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d117050, d118855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d117051 q = 0) : d118856 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117051, d118856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d117051, d118856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d117052 q = 0) : d118857 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117052, d118857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117052, d118857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d117053 q = 0) : d118858 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117053, d118858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117053, d118858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d117056 q = 0) : d118861 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117056, d118861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8886 q selected
    | true =>
      simp only [d117056, d118861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8856 q selected
  have h17 (q : Pattern) (selected : d117057 q = 0) : d118862 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117057, d118862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117057, d118862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d117058 q = 0) : d118863 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117058, d118863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d117058, d118863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d117059 q = 0) : d118864 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117059, d118864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117059, d118864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d117061 q = 0) : d118866 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117061, d118866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8887 q selected
    | true =>
      simp only [d117061, d118866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8857 q selected
  have h21 (q : Pattern) (selected : d117062 q = 0) : d118867 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117062, d118867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117062, d118867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d117063 q = 0) : d118868 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117063, d118868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d117063, d118868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d117065 q = 0) : d118870 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117065, d118870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8888 q selected
    | true =>
      simp only [d117065, d118870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8858 q selected
  have h24 (q : Pattern) (selected : d117067 q = 0) : d118749 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117067, d118749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8889 q selected
    | true =>
      simp only [d117067, d118749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8859 q selected
  have h25 (q : Pattern) (selected : d117068 q = 0) : d118871 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117068, d118871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d117068, d118871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d117070 q = 0) : d118873 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117070, d118873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8890 q selected
    | true =>
      simp only [d117070, d118873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d117071 q = 0) : d118874 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117071, d118874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d117071, d118874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d117072 q = 0) : d118875 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117072, d118875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d117072, d118875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d117073 q = 0) : d118876 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117073, d118876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d117073, d118876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d117074 q = 0) : d118877 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117074, d118877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d117074, d118877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d117075 q = 0) : d118878 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117075, d118878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d117075, d118878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro8892 (p : Pattern) (selected : d117077 p = 0) : d118880 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116872 q = 0) : d118733 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116872, d118733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8850 q selected
    | true =>
      simp only [d116872, d118733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8833 q selected
  have h2 (q : Pattern) (selected : d116981 q = 0) : d118804 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d116981, d118804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116981, d118804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116982 q = 0) : d118805 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d116982, d118805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116982, d118805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116983 q = 0) : d118806 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d116983, d118806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116983, d118806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d116984 q = 0) : d118807 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d116984, d118807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116984, d118807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116771 q = 0) : d118632 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116771, d118632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8833 q selected
    | true =>
      simp only [d116771, d118632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d116828 q = 0) : d118689 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d116828, d118689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116828, d118689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d116829 q = 0) : d118690 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d116829, d118690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d116829, d118690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d116830 q = 0) : d118691 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d116830, d118691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116830, d118691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d116831 q = 0) : d118692 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d116831, d118692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116831, d118692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d117077 q = 0) : d118880 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117077, d118880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117077, d118880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro8893 (p : Pattern) (selected : d117084 p = 0) : d118887 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117065 q = 0) : d118870 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117065, d118870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8888 q selected
    | true =>
      simp only [d117065, d118870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8858 q selected
  have h2 (q : Pattern) (selected : d117067 q = 0) : d118749 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117067, d118749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8889 q selected
    | true =>
      simp only [d117067, d118749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8859 q selected
  have h3 (q : Pattern) (selected : d117068 q = 0) : d118871 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117068, d118871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117068, d118871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117070 q = 0) : d118873 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117070, d118873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8890 q selected
    | true =>
      simp only [d117070, d118873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117071 q = 0) : d118874 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117071, d118874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117071, d118874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117072 q = 0) : d118875 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117072, d118875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117072, d118875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117082 q = 0) : d118885 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117082, d118885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117082, d118885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117083 q = 0) : d118886 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117083, d118886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117083, d118886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d117084 q = 0) : d118887 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117084, d118887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117084, d118887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro8894 (p : Pattern) (selected : d117086 p = 0) : d118889 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116778 q = 0) : d118639 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116778, d118639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8835 q selected
    | true =>
      simp only [d116778, d118639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116835 q = 0) : d118696 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d116835, d118696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116835, d118696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116836 q = 0) : d118697 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d116836, d118697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116836, d118697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116837 q = 0) : d118698 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d116837, d118698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116837, d118698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d116838 q = 0) : d118699 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d116838, d118699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116838, d118699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117086 q = 0) : d118889 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117086, d118889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117086, d118889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro8895 (p : Pattern) (selected : d117096 p = 0) : d118899 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117092 q = 0) : d118895 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117092, d118895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117092, d118895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8876 q selected
  have h2 (q : Pattern) (selected : d117008 q = 0) : d118831 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117008, d118831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8876 q selected
    | true =>
      simp only [d117008, d118831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117093 q = 0) : d118896 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117093, d118896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117093, d118896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117009 q = 0) : d118832 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117009, d118832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117009, d118832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117094 q = 0) : d118897 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117094, d118897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117094, d118897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117095 q = 0) : d118898 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117095, d118898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117095, d118898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d116928 q = 0) : d118769 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116928, d118769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116928, d118769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8847 q selected
  have h8 (q : Pattern) (selected : d116855 q = 0) : d118716 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116855, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8847 q selected
    | true =>
      simp only [d116855, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d116929 q = 0) : d118770 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116929, d118770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d116929, d118770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d116856 q = 0) : d118717 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116856, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d116856, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d116930 q = 0) : d118771 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d116930, d118771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d116930, d118771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d116931 q = 0) : d118772 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d116931, d118772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d116931, d118772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d117096 q = 0) : d118899 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117096, d118899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117096, d118899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro8896 (p : Pattern) (selected : d117102 p = 0) : d118905 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117097 q = 0) : d118900 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117097, d118900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8895 q selected
    | true =>
      simp only [d117097, d118900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8863 q selected
  have h2 (q : Pattern) (selected : d117098 q = 0) : d118901 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117098, d118901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117098, d118901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117099 q = 0) : d118902 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117099, d118902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117099, d118902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116933 q = 0) : d118774 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d116933, d118774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8863 q selected
    | true =>
      simp only [d116933, d118774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8838 q selected
  have h5 (q : Pattern) (selected : d116934 q = 0) : d118775 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d116934, d118775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116934, d118775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116935 q = 0) : d118776 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d116935, d118776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116935, d118776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117100 q = 0) : d118903 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117100, d118903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117100, d118903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d116799 q = 0) : d118660 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d116799, d118660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8838 q selected
    | true =>
      simp only [d116799, d118660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d116800 q = 0) : d118661 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d116800, d118661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116800, d118661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d116801 q = 0) : d118662 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d116801, d118662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116801, d118662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d116936 q = 0) : d118777 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d116936, d118777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d116936, d118777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d117101 q = 0) : d118904 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117101, d118904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117101, d118904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d117102 q = 0) : d118905 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117102, d118905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d117102, d118905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro8897 (p : Pattern) (selected : d117108 p = 0) : d118911 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117103 q = 0) : d118906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117103, d118906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8896 q selected
    | true =>
      simp only [d117103, d118906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117104 q = 0) : d118907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117104, d118907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117104, d118907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116939 q = 0) : d118780 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116939, d118780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8864 q selected
    | true =>
      simp only [d116939, d118780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116940 q = 0) : d118781 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116940, d118781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116940, d118781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117105 q = 0) : d118908 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117105, d118908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117105, d118908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117106 q = 0) : d118909 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117106, d118909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117106, d118909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117107 q = 0) : d118910 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117107, d118910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117107, d118910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117108 q = 0) : d118911 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117108, d118911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117108, d118911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8898 (p : Pattern) (selected : d117114 p = 0) : d118773 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117110 q = 0) : d118769 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117110, d118769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117110, d118769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8880 q selected
  have h2 (q : Pattern) (selected : d117026 q = 0) : d118716 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117026, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8880 q selected
    | true =>
      simp only [d117026, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117111 q = 0) : d118770 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117111, d118770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117111, d118770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117027 q = 0) : d118717 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117027, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117027, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117112 q = 0) : d118771 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117112, d118771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117112, d118771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117113 q = 0) : d118772 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117113, d118772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117113, d118772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d116946 q = 0) : d118655 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116946, d118655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116946, d118655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8851 q selected
  have h8 (q : Pattern) (selected : d116873 q = 0) : d118615 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116873, d118615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8851 q selected
    | true =>
      simp only [d116873, d118615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d116947 q = 0) : d118656 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116947, d118656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d116947, d118656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d116874 q = 0) : d118616 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116874, d118616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d116874, d118616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d116948 q = 0) : d118657 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d116948, d118657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d116948, d118657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d116949 q = 0) : d118658 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d116949, d118658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d116949, d118658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d117114 q = 0) : d118773 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117114, d118773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117114, d118773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro8899 (p : Pattern) (selected : d117120 p = 0) : d118779 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117115 q = 0) : d118774 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117115, d118774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8898 q selected
    | true =>
      simp only [d117115, d118774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8866 q selected
  have h2 (q : Pattern) (selected : d117116 q = 0) : d118775 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117116, d118775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117116, d118775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117117 q = 0) : d118776 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117117, d118776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117117, d118776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116951 q = 0) : d118660 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d116951, d118660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8866 q selected
    | true =>
      simp only [d116951, d118660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116952 q = 0) : d118661 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d116952, d118661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116952, d118661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116953 q = 0) : d118662 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d116953, d118662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116953, d118662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117118 q = 0) : d118777 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117118, d118777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117118, d118777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d116954 q = 0) : d118663 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d116954, d118663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d116954, d118663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117119 q = 0) : d118778 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117119, d118778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117119, d118778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117120 q = 0) : d118779 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117120, d118779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117120, d118779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro8900 (p : Pattern) (selected : d117126 p = 0) : d118785 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117121 q = 0) : d118780 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117121, d118780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8899 q selected
    | true =>
      simp only [d117121, d118780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117122 q = 0) : d118781 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117122, d118781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117122, d118781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116957 q = 0) : d118666 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116957, d118666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8867 q selected
    | true =>
      simp only [d116957, d118666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116958 q = 0) : d118667 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116958, d118667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116958, d118667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117123 q = 0) : d118782 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117123, d118782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117123, d118782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117124 q = 0) : d118783 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117124, d118783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117124, d118783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117125 q = 0) : d118784 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117125, d118784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117125, d118784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117126 q = 0) : d118785 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117126, d118785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117126, d118785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8901 (p : Pattern) (selected : d117132 p = 0) : d118917 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116939 q = 0) : d118780 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116939, d118780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8864 q selected
    | true =>
      simp only [d116939, d118780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116940 q = 0) : d118781 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116940, d118781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116940, d118781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117129 q = 0) : d118914 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117129, d118914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117129, d118914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117130 q = 0) : d118915 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117130, d118915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117130, d118915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117131 q = 0) : d118916 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117131, d118916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117131, d118916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117132 q = 0) : d118917 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117132, d118917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117132, d118917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8902 (p : Pattern) (selected : d117138 p = 0) : d118923 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117109 q = 0) : d118912 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117109, d118912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8897 q selected
    | true =>
      simp only [d117109, d118912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8865 q selected
  have h2 (q : Pattern) (selected : d117127 q = 0) : d118786 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117127, d118786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8900 q selected
    | true =>
      simp only [d117127, d118786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8868 q selected
  have h3 (q : Pattern) (selected : d117128 q = 0) : d118913 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117128, d118913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117128, d118913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117133 q = 0) : d118918 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117133, d118918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8901 q selected
    | true =>
      simp only [d117133, d118918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117134 q = 0) : d118919 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117134, d118919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117134, d118919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117135 q = 0) : d118920 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117135, d118920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117135, d118920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117136 q = 0) : d118921 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117136, d118921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117136, d118921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117137 q = 0) : d118922 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117137, d118922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117137, d118922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d117138 q = 0) : d118923 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117138, d118923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117138, d118923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro8903 (p : Pattern) (selected : d117144 p = 0) : d118929 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116811 q = 0) : d118672 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116811, d118672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8840 q selected
    | true =>
      simp only [d116811, d118672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117140 q = 0) : d118925 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117140, d118925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117140, d118925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117141 q = 0) : d118926 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117141, d118926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117141, d118926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117142 q = 0) : d118927 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117142, d118927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117142, d118927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117143 q = 0) : d118928 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117143, d118928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117143, d118928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117144 q = 0) : d118929 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117144, d118929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117144, d118929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro8904 (p : Pattern) (selected : d117150 p = 0) : d118935 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116986 q = 0) : d118809 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d116986, d118809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116986, d118809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8872 q selected
  have h2 (q : Pattern) (selected : d116987 q = 0) : d118810 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d116987, d118810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d116987, d118810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d116993 q = 0) : d118816 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d116993, d118816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8872 q selected
    | true =>
      simp only [d116993, d118816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8873 q selected
  have h4 (q : Pattern) (selected : d116994 q = 0) : d118817 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d116994, d118817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116994, d118817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116995 q = 0) : d118818 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d116995, d118818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116995, d118818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117076 q = 0) : d118879 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d117076, d118879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8885 q selected
    | true =>
      simp only [d117076, d118879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8891 q selected
  have h7 (q : Pattern) (selected : d117078 q = 0) : d118881 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d117078, d118881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8892 q selected
    | true =>
      simp only [d117078, d118881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8844 q selected
  have h8 (q : Pattern) (selected : d117079 q = 0) : d118882 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d117079, d118882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117079, d118882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d117080 q = 0) : d118883 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d117080, d118883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117080, d118883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d117081 q = 0) : d118884 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d117081, d118884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117081, d118884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d117085 q = 0) : d118888 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d117085, d118888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117085, d118888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8893 q selected
  have h12 (q : Pattern) (selected : d117087 q = 0) : d118890 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d117087, d118890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117087, d118890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8894 q selected
  have h13 (q : Pattern) (selected : d117088 q = 0) : d118891 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d117088, d118891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d117088, d118891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d117089 q = 0) : d118892 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d117089, d118892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d117089, d118892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d117090 q = 0) : d118893 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d117090, d118893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d117090, d118893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d117091 q = 0) : d118894 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d117091, d118894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d117091, d118894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d117139 q = 0) : d118924 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d117139, d118924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117139, d118924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8902 q selected
  have h18 (q : Pattern) (selected : d117145 q = 0) : d118930 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d117145, d118930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117145, d118930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8903 q selected
  have h19 (q : Pattern) (selected : d117146 q = 0) : d118931 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d117146, d118931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d117146, d118931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d117147 q = 0) : d118932 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d117147, d118932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d117147, d118932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d117148 q = 0) : d118933 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d117148, d118933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d117148, d118933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d117149 q = 0) : d118934 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d117149, d118934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d117149, d118934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d117150 q = 0) : d118935 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d117150, d118935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d117150, d118935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro8905 (p : Pattern) (selected : d117156 p = 0) : d118941 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117151 q = 0) : d118936 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d117151, d118936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117151, d118936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8904 q selected
  have h2 (q : Pattern) (selected : d117152 q = 0) : d118937 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d117152, d118937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117152, d118937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117153 q = 0) : d118938 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d117153, d118938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117153, d118938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117154 q = 0) : d118939 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d117154, d118939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117154, d118939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117155 q = 0) : d118940 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d117155, d118940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117155, d118940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117156 q = 0) : d118941 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d117156, d118941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117156, d118941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro8906 (p : Pattern) (selected : d117158 p = 0) : d118943 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116855 q = 0) : d118716 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116855, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8847 q selected
    | true =>
      simp only [d116855, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116856 q = 0) : d118717 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116856, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d116856, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d116857 q = 0) : d118718 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d116857, d118718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116857, d118718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116858 q = 0) : d118719 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d116858, d118719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116858, d118719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117158 q = 0) : d118943 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117158, d118943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117158, d118943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro8907 (p : Pattern) (selected : d117168 p = 0) : d118953 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117159 q = 0) : d118944 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117159, d118944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8877 q selected
    | true =>
      simp only [d117159, d118944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8906 q selected
  have h2 (q : Pattern) (selected : d117160 q = 0) : d118945 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117160, d118945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117160, d118945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117161 q = 0) : d118946 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117161, d118946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117161, d118946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117162 q = 0) : d118947 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117162, d118947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8906 q selected
    | true =>
      simp only [d117162, d118947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117163 q = 0) : d118948 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117163, d118948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117163, d118948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117164 q = 0) : d118949 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117164, d118949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117164, d118949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117165 q = 0) : d118950 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117165, d118950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117165, d118950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117166 q = 0) : d118951 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117166, d118951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117166, d118951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117167 q = 0) : d118952 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117167, d118952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117167, d118952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117168 q = 0) : d118953 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117168, d118953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117168, d118953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro8908 (p : Pattern) (selected : d117172 p = 0) : d118957 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117162 q = 0) : d118947 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117162, d118947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8906 q selected
    | true =>
      simp only [d117162, d118947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117163 q = 0) : d118948 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117163, d118948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117163, d118948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117164 q = 0) : d118949 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117164, d118949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117164, d118949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117166 q = 0) : d118951 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117166, d118951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117166, d118951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117171 q = 0) : d118956 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117171, d118956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117171, d118956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117172 q = 0) : d118957 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117172, d118957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117172, d118957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8909 (p : Pattern) (selected : d117178 p = 0) : d118963 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117169 q = 0) : d118954 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117169, d118954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8907 q selected
    | true =>
      simp only [d117169, d118954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117170 q = 0) : d118955 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117170, d118955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117170, d118955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117173 q = 0) : d118958 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117173, d118958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8908 q selected
    | true =>
      simp only [d117173, d118958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117174 q = 0) : d118959 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117174, d118959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117174, d118959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117175 q = 0) : d118960 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117175, d118960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117175, d118960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117176 q = 0) : d118961 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117176, d118961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117176, d118961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117177 q = 0) : d118962 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117177, d118962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117177, d118962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117178 q = 0) : d118963 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117178, d118963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117178, d118963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro8910 (p : Pattern) (selected : d117182 p = 0) : d118967 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117173 q = 0) : d118958 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117173, d118958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8908 q selected
    | true =>
      simp only [d117173, d118958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117174 q = 0) : d118959 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117174, d118959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117174, d118959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117179 q = 0) : d118964 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117179, d118964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117179, d118964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117180 q = 0) : d118965 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117180, d118965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117180, d118965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117181 q = 0) : d118966 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117181, d118966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117181, d118966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117182 q = 0) : d118967 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117182, d118967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117182, d118967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro8911 (p : Pattern) (selected : d117188 p = 0) : d118973 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117183 q = 0) : d118968 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117183, d118968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8909 q selected
    | true =>
      simp only [d117183, d118968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8910 q selected
  have h2 (q : Pattern) (selected : d117184 q = 0) : d118969 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117184, d118969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117184, d118969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117185 q = 0) : d118970 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117185, d118970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117185, d118970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117186 q = 0) : d118971 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117186, d118971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117186, d118971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117187 q = 0) : d118972 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117187, d118972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117187, d118972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117188 q = 0) : d118973 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117188, d118973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117188, d118973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro8912 (p : Pattern) (selected : d117191 p = 0) : d118976 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117169 q = 0) : d118954 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117169, d118954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8907 q selected
    | true =>
      simp only [d117169, d118954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117170 q = 0) : d118955 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117170, d118955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117170, d118955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117173 q = 0) : d118958 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117173, d118958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8908 q selected
    | true =>
      simp only [d117173, d118958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117174 q = 0) : d118959 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117174, d118959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117174, d118959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117175 q = 0) : d118960 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117175, d118960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117175, d118960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117176 q = 0) : d118961 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117176, d118961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117176, d118961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117177 q = 0) : d118962 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117177, d118962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117177, d118962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117191 q = 0) : d118976 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117191, d118976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117191, d118976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8913 (p : Pattern) (selected : d117192 p = 0) : d118977 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117173 q = 0) : d118958 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117173, d118958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8908 q selected
    | true =>
      simp only [d117173, d118958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117174 q = 0) : d118959 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117174, d118959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117174, d118959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117179 q = 0) : d118964 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117179, d118964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117179, d118964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117180 q = 0) : d118965 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117180, d118965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117180, d118965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117181 q = 0) : d118966 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117181, d118966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117181, d118966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117192 q = 0) : d118977 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117192, d118977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117192, d118977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8914 (p : Pattern) (selected : d117198 p = 0) : d118983 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117183 q = 0) : d118968 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117183, d118968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8909 q selected
    | true =>
      simp only [d117183, d118968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8910 q selected
  have h2 (q : Pattern) (selected : d117184 q = 0) : d118969 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117184, d118969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117184, d118969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117185 q = 0) : d118970 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117185, d118970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117185, d118970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117186 q = 0) : d118971 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117186, d118971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117186, d118971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117187 q = 0) : d118972 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117187, d118972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117187, d118972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117193 q = 0) : d118978 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117193, d118978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8912 q selected
    | true =>
      simp only [d117193, d118978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8913 q selected
  have h7 (q : Pattern) (selected : d117194 q = 0) : d118979 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117194, d118979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117194, d118979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117195 q = 0) : d118980 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117195, d118980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117195, d118980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117196 q = 0) : d118981 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117196, d118981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117196, d118981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117197 q = 0) : d118982 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117197, d118982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117197, d118982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d117198 q = 0) : d118983 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117198, d118983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117198, d118983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro8915 (p : Pattern) (selected : d117203 p = 0) : d118988 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117169 q = 0) : d118954 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117169, d118954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8907 q selected
    | true =>
      simp only [d117169, d118954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117170 q = 0) : d118955 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117170, d118955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117170, d118955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117173 q = 0) : d118958 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117173, d118958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8908 q selected
    | true =>
      simp only [d117173, d118958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117174 q = 0) : d118959 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117174, d118959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117174, d118959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117175 q = 0) : d118960 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117175, d118960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117175, d118960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117176 q = 0) : d118961 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117176, d118961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117176, d118961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117202 q = 0) : d118987 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117202, d118987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117202, d118987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117203 q = 0) : d118988 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117203, d118988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117203, d118988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro8916 (p : Pattern) (selected : d117205 p = 0) : d118990 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117173 q = 0) : d118958 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117173, d118958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8908 q selected
    | true =>
      simp only [d117173, d118958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117174 q = 0) : d118959 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117174, d118959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117174, d118959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117179 q = 0) : d118964 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117179, d118964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117179, d118964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117180 q = 0) : d118965 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117180, d118965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117180, d118965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117204 q = 0) : d118989 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117204, d118989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117204, d118989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117205 q = 0) : d118990 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117205, d118990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117205, d118990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro8917 (p : Pattern) (selected : d117212 p = 0) : d118997 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117169 q = 0) : d118954 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117169, d118954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8907 q selected
    | true =>
      simp only [d117169, d118954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117170 q = 0) : d118955 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117170, d118955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117170, d118955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117173 q = 0) : d118958 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117173, d118958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8908 q selected
    | true =>
      simp only [d117173, d118958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117174 q = 0) : d118959 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117174, d118959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117174, d118959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117175 q = 0) : d118960 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117175, d118960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117175, d118960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117210 q = 0) : d118995 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117210, d118995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117210, d118995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117211 q = 0) : d118996 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117211, d118996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117211, d118996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117212 q = 0) : d118997 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117212, d118997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117212, d118997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro8918 (p : Pattern) (selected : d117215 p = 0) : d119000 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117173 q = 0) : d118958 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117173, d118958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8908 q selected
    | true =>
      simp only [d117173, d118958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117174 q = 0) : d118959 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117174, d118959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117174, d118959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117179 q = 0) : d118964 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117179, d118964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117179, d118964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117213 q = 0) : d118998 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117213, d118998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117213, d118998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117214 q = 0) : d118999 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117214, d118999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117214, d118999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117215 q = 0) : d119000 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117215, d119000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117215, d119000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro8919 (p : Pattern) (selected : d541 p = 0) : d52288 p = 1 := by
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
  have h3 (q : Pattern) (selected : d313 q = 0) : d52112 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d52112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro234 q selected
    | true =>
      simp only [d313, d52112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314 q = 0) : d52113 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d52113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314, d52113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d533 q = 0) : d52280 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d533, d52280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d533, d52280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d537 q = 0) : d52284 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d537, d52284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro276 q selected
    | true =>
      simp only [d537, d52284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d538 q = 0) : d52285 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d538, d52285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d538, d52285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133 q = 0) : d51984 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro204 q selected
    | true =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d134 q = 0) : d51985 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d539 q = 0) : d52286 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d539, d52286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d539, d52286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d540 q = 0) : d52287 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d540, d52287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d540, d52287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d541 q = 0) : d52288 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d541, d52288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d541, d52288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h12 p selected
theorem eqIntro8920 (p : Pattern) (selected : d117223 p = 0) : d119008 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117219 q = 0) : d119004 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117219, d119004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8919 q selected
    | true =>
      simp only [d117219, d119004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117220 q = 0) : d119005 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117220, d119005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117220, d119005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117221 q = 0) : d119006 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117221, d119006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117221, d119006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117222 q = 0) : d119007 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117222, d119007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117222, d119007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117008 q = 0) : d118831 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117008, d118831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8876 q selected
    | true =>
      simp only [d117008, d118831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117009 q = 0) : d118832 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117009, d118832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117009, d118832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117010 q = 0) : d118833 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117010, d118833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117010, d118833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117011 q = 0) : d118834 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117011, d118834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117011, d118834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117223 q = 0) : d119008 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117223, d119008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117223, d119008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro8921 (p : Pattern) (selected : d9456 p = 0) : d101071 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9452 q = 0) : d101067 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9452, d101067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2798 q selected
    | true =>
      simp only [d9452, d101067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9453 q = 0) : d101068 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d101068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9453, d101068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
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
  have h5 (q : Pattern) (selected : d9454 q = 0) : d101069 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9454, d101069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9454, d101069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9455 q = 0) : d101070 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9455, d101070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9455, d101070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9456 q = 0) : d101071 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9456, d101071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9456, d101071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro8922 (p : Pattern) (selected : d117231 p = 0) : d119016 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117227 q = 0) : d119012 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117227, d119012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8921 q selected
    | true =>
      simp only [d117227, d119012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117228 q = 0) : d119013 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117228, d119013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117228, d119013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117229 q = 0) : d119014 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117229, d119014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117229, d119014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117230 q = 0) : d119015 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117230, d119015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117230, d119015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117231 q = 0) : d119016 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117231, d119016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117231, d119016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro8923 (p : Pattern) (selected : d117237 p = 0) : d119022 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117224 q = 0) : d119009 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117224, d119009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8920 q selected
    | true =>
      simp only [d117224, d119009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8877 q selected
  have h2 (q : Pattern) (selected : d117225 q = 0) : d119010 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117225, d119010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117225, d119010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117226 q = 0) : d119011 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117226, d119011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117226, d119011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117232 q = 0) : d119017 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117232, d119017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8877 q selected
    | true =>
      simp only [d117232, d119017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8922 q selected
  have h5 (q : Pattern) (selected : d117233 q = 0) : d119018 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117233, d119018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117233, d119018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117234 q = 0) : d119019 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117234, d119019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117234, d119019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117235 q = 0) : d119020 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117235, d119020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117235, d119020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117159 q = 0) : d118944 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117159, d118944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8877 q selected
    | true =>
      simp only [d117159, d118944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8906 q selected
  have h9 (q : Pattern) (selected : d117160 q = 0) : d118945 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117160, d118945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117160, d118945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117161 q = 0) : d118946 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117161, d118946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117161, d118946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d117162 q = 0) : d118947 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117162, d118947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8906 q selected
    | true =>
      simp only [d117162, d118947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d117163 q = 0) : d118948 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117163, d118948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117163, d118948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d117164 q = 0) : d118949 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117164, d118949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117164, d118949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d117165 q = 0) : d118950 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117165, d118950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d117165, d118950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d117236 q = 0) : d119021 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117236, d119021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117236, d119021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d117237 q = 0) : d119022 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117237, d119022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d117237, d119022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro8924 (p : Pattern) (selected : d117243 p = 0) : d119028 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117238 q = 0) : d119023 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117238, d119023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8923 q selected
    | true =>
      simp only [d117238, d119023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117239 q = 0) : d119024 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117239, d119024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117239, d119024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117169 q = 0) : d118954 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117169, d118954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8907 q selected
    | true =>
      simp only [d117169, d118954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117170 q = 0) : d118955 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117170, d118955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117170, d118955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117240 q = 0) : d119025 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117240, d119025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117240, d119025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117241 q = 0) : d119026 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117241, d119026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117241, d119026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117242 q = 0) : d119027 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117242, d119027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117242, d119027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117243 q = 0) : d119028 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117243, d119028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117243, d119028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro8925 (p : Pattern) (selected : d572 p = 0) : d52116 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d568 q = 0) : d52112 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d568, d52112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro281 q selected
    | true =>
      simp only [d568, d52112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d569 q = 0) : d52113 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d569, d52113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d569, d52113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
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
  have h5 (q : Pattern) (selected : d570 q = 0) : d52114 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d570, d52114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d570, d52114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164 q = 0) : d51871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
    | true =>
      simp only [d164, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d165 q = 0) : d51872 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d165, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d165, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d346 q = 0) : d51986 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d346, d51986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d346, d51986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d571 q = 0) : d52115 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d571, d52115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d571, d52115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d572 q = 0) : d52116 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d572, d52116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d572, d52116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro8926 (p : Pattern) (selected : d117249 p = 0) : d118835 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117245 q = 0) : d118831 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117245, d118831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8925 q selected
    | true =>
      simp only [d117245, d118831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117246 q = 0) : d118832 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117246, d118832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117246, d118832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117247 q = 0) : d118833 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117247, d118833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117247, d118833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117248 q = 0) : d118834 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117248, d118834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117248, d118834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117026 q = 0) : d118716 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117026, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8880 q selected
    | true =>
      simp only [d117026, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117027 q = 0) : d118717 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117027, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117027, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117028 q = 0) : d118718 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117028, d118718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117028, d118718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117029 q = 0) : d118719 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117029, d118719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117029, d118719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117249 q = 0) : d118835 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117249, d118835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117249, d118835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro8927 (p : Pattern) (selected : d117250 p = 0) : d118943 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117026 q = 0) : d118716 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117026, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8880 q selected
    | true =>
      simp only [d117026, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117027 q = 0) : d118717 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117027, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117027, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117028 q = 0) : d118718 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117028, d118718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117028, d118718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117029 q = 0) : d118719 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117029, d118719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117029, d118719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117250 q = 0) : d118943 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117250, d118943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117250, d118943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro8928 (p : Pattern) (selected : d117260 p = 0) : d118953 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117251 q = 0) : d118944 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117251, d118944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8926 q selected
    | true =>
      simp only [d117251, d118944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8927 q selected
  have h2 (q : Pattern) (selected : d117252 q = 0) : d118945 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117252, d118945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117252, d118945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117253 q = 0) : d118946 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117253, d118946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117253, d118946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117254 q = 0) : d118947 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117254, d118947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8927 q selected
    | true =>
      simp only [d117254, d118947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117255 q = 0) : d118948 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117255, d118948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117255, d118948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117256 q = 0) : d118949 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117256, d118949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117256, d118949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117257 q = 0) : d118950 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117257, d118950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117257, d118950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117258 q = 0) : d118951 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117258, d118951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117258, d118951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117259 q = 0) : d118952 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117259, d118952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117259, d118952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117260 q = 0) : d118953 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117260, d118953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117260, d118953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro8929 (p : Pattern) (selected : d117264 p = 0) : d118957 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117254 q = 0) : d118947 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117254, d118947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8927 q selected
    | true =>
      simp only [d117254, d118947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117255 q = 0) : d118948 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117255, d118948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117255, d118948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117256 q = 0) : d118949 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117256, d118949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117256, d118949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117258 q = 0) : d118951 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117258, d118951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117258, d118951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117263 q = 0) : d118956 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117263, d118956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117263, d118956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117264 q = 0) : d118957 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117264, d118957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117264, d118957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8930 (p : Pattern) (selected : d117270 p = 0) : d118963 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117261 q = 0) : d118954 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117261, d118954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8928 q selected
    | true =>
      simp only [d117261, d118954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117262 q = 0) : d118955 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117262, d118955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117262, d118955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117265 q = 0) : d118958 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117265, d118958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8929 q selected
    | true =>
      simp only [d117265, d118958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117266 q = 0) : d118959 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117266, d118959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117266, d118959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117267 q = 0) : d118960 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117267, d118960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117267, d118960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117268 q = 0) : d118961 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117268, d118961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117268, d118961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117269 q = 0) : d118962 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117269, d118962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117269, d118962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117270 q = 0) : d118963 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117270, d118963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117270, d118963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro8931 (p : Pattern) (selected : d117274 p = 0) : d118967 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117265 q = 0) : d118958 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117265, d118958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8929 q selected
    | true =>
      simp only [d117265, d118958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117266 q = 0) : d118959 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117266, d118959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117266, d118959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117271 q = 0) : d118964 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117271, d118964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117271, d118964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117272 q = 0) : d118965 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117272, d118965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117272, d118965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117273 q = 0) : d118966 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117273, d118966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117273, d118966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117274 q = 0) : d118967 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117274, d118967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117274, d118967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro8932 (p : Pattern) (selected : d117280 p = 0) : d119034 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117169 q = 0) : d118954 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117169, d118954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8907 q selected
    | true =>
      simp only [d117169, d118954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117170 q = 0) : d118955 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117170, d118955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117170, d118955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117277 q = 0) : d119031 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117277, d119031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117277, d119031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117278 q = 0) : d119032 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117278, d119032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117278, d119032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117279 q = 0) : d119033 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117279, d119033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117279, d119033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117280 q = 0) : d119034 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117280, d119034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117280, d119034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro8933 (p : Pattern) (selected : d117286 p = 0) : d119040 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117206 q = 0) : d118991 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117206, d118991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8915 q selected
    | true =>
      simp only [d117206, d118991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8916 q selected
  have h2 (q : Pattern) (selected : d117207 q = 0) : d118992 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117207, d118992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117207, d118992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117208 q = 0) : d118993 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117208, d118993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117208, d118993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117209 q = 0) : d118994 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117209, d118994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117209, d118994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117216 q = 0) : d119001 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117216, d119001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8917 q selected
    | true =>
      simp only [d117216, d119001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8918 q selected
  have h6 (q : Pattern) (selected : d117217 q = 0) : d119002 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117217, d119002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117217, d119002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117218 q = 0) : d119003 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117218, d119003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117218, d119003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117244 q = 0) : d119029 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117244, d119029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8924 q selected
    | true =>
      simp only [d117244, d119029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8909 q selected
  have h9 (q : Pattern) (selected : d117275 q = 0) : d118968 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117275, d118968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8930 q selected
    | true =>
      simp only [d117275, d118968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8931 q selected
  have h10 (q : Pattern) (selected : d117276 q = 0) : d119030 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117276, d119030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117276, d119030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d117281 q = 0) : d119035 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117281, d119035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8932 q selected
    | true =>
      simp only [d117281, d119035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d117282 q = 0) : d119036 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117282, d119036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d117282, d119036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d117283 q = 0) : d119037 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117283, d119037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d117283, d119037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d117284 q = 0) : d119038 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117284, d119038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117284, d119038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d117285 q = 0) : d119039 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117285, d119039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117285, d119039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d117286 q = 0) : d119040 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117286, d119040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117286, d119040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro8934 (p : Pattern) (selected : d117287 p = 0) : d119041 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117169 q = 0) : d118954 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117169, d118954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8907 q selected
    | true =>
      simp only [d117169, d118954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117170 q = 0) : d118955 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117170, d118955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117170, d118955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117173 q = 0) : d118958 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117173, d118958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8908 q selected
    | true =>
      simp only [d117173, d118958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117174 q = 0) : d118959 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117174, d118959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117174, d118959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117175 q = 0) : d118960 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117175, d118960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117175, d118960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117176 q = 0) : d118961 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117176, d118961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117176, d118961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117202 q = 0) : d118987 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117202, d118987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117202, d118987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117287 q = 0) : d119041 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117287, d119041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117287, d119041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8935 (p : Pattern) (selected : d117288 p = 0) : d119042 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117173 q = 0) : d118958 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117173, d118958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8908 q selected
    | true =>
      simp only [d117173, d118958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117174 q = 0) : d118959 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117174, d118959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117174, d118959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117179 q = 0) : d118964 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117179, d118964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117179, d118964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117180 q = 0) : d118965 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117180, d118965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117180, d118965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117204 q = 0) : d118989 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117204, d118989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117204, d118989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117288 q = 0) : d119042 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117288, d119042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117288, d119042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8936 (p : Pattern) (selected : d117293 p = 0) : d119047 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117169 q = 0) : d118954 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117169, d118954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8907 q selected
    | true =>
      simp only [d117169, d118954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117170 q = 0) : d118955 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117170, d118955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117170, d118955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117173 q = 0) : d118958 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117173, d118958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8908 q selected
    | true =>
      simp only [d117173, d118958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117174 q = 0) : d118959 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117174, d118959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117174, d118959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117175 q = 0) : d118960 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117175, d118960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117175, d118960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117210 q = 0) : d118995 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117210, d118995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117210, d118995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117211 q = 0) : d118996 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117211, d118996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117211, d118996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117293 q = 0) : d119047 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117293, d119047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117293, d119047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8937 (p : Pattern) (selected : d117294 p = 0) : d119048 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117173 q = 0) : d118958 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117173, d118958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8908 q selected
    | true =>
      simp only [d117173, d118958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117174 q = 0) : d118959 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117174, d118959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117174, d118959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117179 q = 0) : d118964 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117179, d118964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117179, d118964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117213 q = 0) : d118998 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117213, d118998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117213, d118998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117214 q = 0) : d118999 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117214, d118999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117214, d118999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117294 q = 0) : d119048 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117294, d119048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117294, d119048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8938 (p : Pattern) (selected : d117298 p = 0) : d119052 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117238 q = 0) : d119023 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117238, d119023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8923 q selected
    | true =>
      simp only [d117238, d119023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117239 q = 0) : d119024 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117239, d119024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117239, d119024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117169 q = 0) : d118954 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117169, d118954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8907 q selected
    | true =>
      simp only [d117169, d118954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117170 q = 0) : d118955 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117170, d118955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117170, d118955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117240 q = 0) : d119025 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117240, d119025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117240, d119025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117241 q = 0) : d119026 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117241, d119026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117241, d119026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117242 q = 0) : d119027 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117242, d119027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117242, d119027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117298 q = 0) : d119052 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117298, d119052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117298, d119052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8939 (p : Pattern) (selected : d117300 p = 0) : d118976 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117261 q = 0) : d118954 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117261, d118954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8928 q selected
    | true =>
      simp only [d117261, d118954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117262 q = 0) : d118955 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117262, d118955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117262, d118955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117265 q = 0) : d118958 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117265, d118958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8929 q selected
    | true =>
      simp only [d117265, d118958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117266 q = 0) : d118959 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117266, d118959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117266, d118959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117267 q = 0) : d118960 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117267, d118960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117267, d118960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117268 q = 0) : d118961 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117268, d118961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117268, d118961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117269 q = 0) : d118962 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117269, d118962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117269, d118962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117300 q = 0) : d118976 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117300, d118976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117300, d118976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8940 (p : Pattern) (selected : d117301 p = 0) : d118977 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117265 q = 0) : d118958 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117265, d118958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8929 q selected
    | true =>
      simp only [d117265, d118958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117266 q = 0) : d118959 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117266, d118959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117266, d118959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117271 q = 0) : d118964 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117271, d118964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117271, d118964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117272 q = 0) : d118965 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117272, d118965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117272, d118965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117273 q = 0) : d118966 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117273, d118966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117273, d118966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117301 q = 0) : d118977 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117301, d118977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117301, d118977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8941 (p : Pattern) (selected : d117304 p = 0) : d119055 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117169 q = 0) : d118954 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117169, d118954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8907 q selected
    | true =>
      simp only [d117169, d118954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117170 q = 0) : d118955 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117170, d118955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117170, d118955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117277 q = 0) : d119031 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117277, d119031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117277, d119031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117278 q = 0) : d119032 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117278, d119032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117278, d119032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117279 q = 0) : d119033 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117279, d119033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117279, d119033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117304 q = 0) : d119055 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117304, d119055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117304, d119055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8942 (p : Pattern) (selected : d117310 p = 0) : d119061 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117206 q = 0) : d118991 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117206, d118991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8915 q selected
    | true =>
      simp only [d117206, d118991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8916 q selected
  have h2 (q : Pattern) (selected : d117207 q = 0) : d118992 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117207, d118992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117207, d118992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117208 q = 0) : d118993 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117208, d118993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117208, d118993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117209 q = 0) : d118994 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117209, d118994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117209, d118994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117216 q = 0) : d119001 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117216, d119001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8917 q selected
    | true =>
      simp only [d117216, d119001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8918 q selected
  have h6 (q : Pattern) (selected : d117217 q = 0) : d119002 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117217, d119002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117217, d119002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117218 q = 0) : d119003 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117218, d119003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117218, d119003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117244 q = 0) : d119029 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117244, d119029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8924 q selected
    | true =>
      simp only [d117244, d119029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8909 q selected
  have h9 (q : Pattern) (selected : d117275 q = 0) : d118968 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117275, d118968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8930 q selected
    | true =>
      simp only [d117275, d118968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8931 q selected
  have h10 (q : Pattern) (selected : d117276 q = 0) : d119030 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117276, d119030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117276, d119030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d117281 q = 0) : d119035 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117281, d119035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8932 q selected
    | true =>
      simp only [d117281, d119035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d117282 q = 0) : d119036 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117282, d119036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d117282, d119036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d117283 q = 0) : d119037 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117283, d119037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d117283, d119037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d117284 q = 0) : d119038 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117284, d119038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117284, d119038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d117285 q = 0) : d119039 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117285, d119039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117285, d119039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d117289 q = 0) : d119043 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117289, d119043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8934 q selected
    | true =>
      simp only [d117289, d119043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8935 q selected
  have h17 (q : Pattern) (selected : d117290 q = 0) : d119044 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117290, d119044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117290, d119044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d117291 q = 0) : d119045 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117291, d119045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d117291, d119045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d117292 q = 0) : d119046 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117292, d119046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117292, d119046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d117295 q = 0) : d119049 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117295, d119049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8936 q selected
    | true =>
      simp only [d117295, d119049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8937 q selected
  have h21 (q : Pattern) (selected : d117296 q = 0) : d119050 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117296, d119050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117296, d119050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d117297 q = 0) : d119051 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117297, d119051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d117297, d119051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d117299 q = 0) : d119053 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117299, d119053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8938 q selected
    | true =>
      simp only [d117299, d119053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8912 q selected
  have h24 (q : Pattern) (selected : d117302 q = 0) : d118978 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117302, d118978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8939 q selected
    | true =>
      simp only [d117302, d118978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8940 q selected
  have h25 (q : Pattern) (selected : d117303 q = 0) : d119054 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117303, d119054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d117303, d119054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d117305 q = 0) : d119056 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117305, d119056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8941 q selected
    | true =>
      simp only [d117305, d119056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d117306 q = 0) : d119057 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117306, d119057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d117306, d119057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d117307 q = 0) : d119058 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117307, d119058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d117307, d119058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d117308 q = 0) : d119059 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117308, d119059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d117308, d119059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d117309 q = 0) : d119060 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117309, d119060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d117309, d119060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d117310 q = 0) : d119061 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117310, d119061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d117310, d119061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro8943 (p : Pattern) (selected : d117317 p = 0) : d119068 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117183 q = 0) : d118968 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117183, d118968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8909 q selected
    | true =>
      simp only [d117183, d118968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8910 q selected
  have h2 (q : Pattern) (selected : d117184 q = 0) : d118969 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117184, d118969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117184, d118969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117185 q = 0) : d118970 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117185, d118970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117185, d118970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117186 q = 0) : d118971 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117186, d118971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117186, d118971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117187 q = 0) : d118972 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117187, d118972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117187, d118972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117312 q = 0) : d119063 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117312, d119063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8910 q selected
    | true =>
      simp only [d117312, d119063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117313 q = 0) : d119064 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117313, d119064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117313, d119064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117314 q = 0) : d119065 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117314, d119065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117314, d119065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117315 q = 0) : d119066 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117315, d119066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117315, d119066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117316 q = 0) : d119067 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117316, d119067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117316, d119067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d117317 q = 0) : d119068 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117317, d119068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117317, d119068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro8944 (p : Pattern) (selected : d117323 p = 0) : d119074 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117312 q = 0) : d119063 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117312, d119063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8910 q selected
    | true =>
      simp only [d117312, d119063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117313 q = 0) : d119064 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117313, d119064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117313, d119064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117314 q = 0) : d119065 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117314, d119065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117314, d119065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117315 q = 0) : d119066 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117315, d119066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117315, d119066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117316 q = 0) : d119067 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117316, d119067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117316, d119067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117318 q = 0) : d119069 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117318, d119069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8913 q selected
    | true =>
      simp only [d117318, d119069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117319 q = 0) : d119070 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117319, d119070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117319, d119070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117320 q = 0) : d119071 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117320, d119071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117320, d119071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117321 q = 0) : d119072 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117321, d119072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117321, d119072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117322 q = 0) : d119073 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117322, d119073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117322, d119073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d117323 q = 0) : d119074 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117323, d119074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117323, d119074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro8945 (p : Pattern) (selected : d117330 p = 0) : d119081 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117299 q = 0) : d119053 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117299, d119053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8938 q selected
    | true =>
      simp only [d117299, d119053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8912 q selected
  have h2 (q : Pattern) (selected : d117302 q = 0) : d118978 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117302, d118978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8939 q selected
    | true =>
      simp only [d117302, d118978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8940 q selected
  have h3 (q : Pattern) (selected : d117303 q = 0) : d119054 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117303, d119054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117303, d119054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117305 q = 0) : d119056 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117305, d119056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8941 q selected
    | true =>
      simp only [d117305, d119056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117306 q = 0) : d119057 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117306, d119057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117306, d119057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117307 q = 0) : d119058 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117307, d119058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117307, d119058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117328 q = 0) : d119079 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117328, d119079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117328, d119079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117329 q = 0) : d119080 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117329, d119080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117329, d119080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d117330 q = 0) : d119081 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117330, d119081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117330, d119081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro8946 (p : Pattern) (selected : d117332 p = 0) : d119083 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117318 q = 0) : d119069 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117318, d119069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8913 q selected
    | true =>
      simp only [d117318, d119069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117319 q = 0) : d119070 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117319, d119070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117319, d119070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117320 q = 0) : d119071 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117320, d119071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117320, d119071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117321 q = 0) : d119072 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117321, d119072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117321, d119072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117322 q = 0) : d119073 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117322, d119073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117322, d119073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117332 q = 0) : d119083 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117332, d119083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117332, d119083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro8947 (p : Pattern) (selected : d117342 p = 0) : d119093 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117338 q = 0) : d119089 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117338, d119089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117338, d119089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8919 q selected
  have h2 (q : Pattern) (selected : d117219 q = 0) : d119004 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117219, d119004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8919 q selected
    | true =>
      simp only [d117219, d119004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117339 q = 0) : d119090 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117339, d119090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117339, d119090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117220 q = 0) : d119005 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117220, d119005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117220, d119005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117340 q = 0) : d119091 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117340, d119091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117340, d119091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117341 q = 0) : d119092 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117341, d119092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117341, d119092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117092 q = 0) : d118895 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117092, d118895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117092, d118895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8876 q selected
  have h8 (q : Pattern) (selected : d117008 q = 0) : d118831 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117008, d118831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8876 q selected
    | true =>
      simp only [d117008, d118831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117093 q = 0) : d118896 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117093, d118896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117093, d118896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117009 q = 0) : d118832 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117009, d118832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117009, d118832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d117094 q = 0) : d118897 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117094, d118897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117094, d118897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d117095 q = 0) : d118898 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117095, d118898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d117095, d118898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d117342 q = 0) : d119093 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117342, d119093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117342, d119093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro8948 (p : Pattern) (selected : d117350 p = 0) : d119101 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117346 q = 0) : d119097 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117346, d119097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117346, d119097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8921 q selected
  have h2 (q : Pattern) (selected : d117227 q = 0) : d119012 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117227, d119012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8921 q selected
    | true =>
      simp only [d117227, d119012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117347 q = 0) : d119098 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117347, d119098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117347, d119098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117228 q = 0) : d119013 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117228, d119013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117228, d119013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117348 q = 0) : d119099 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117348, d119099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117348, d119099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117349 q = 0) : d119100 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117349, d119100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117349, d119100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117350 q = 0) : d119101 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117350, d119101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117350, d119101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro8949 (p : Pattern) (selected : d117355 p = 0) : d119106 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d116928 q = 0) : d118769 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116928, d118769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116928, d118769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8847 q selected
  have h2 (q : Pattern) (selected : d116855 q = 0) : d118716 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116855, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8847 q selected
    | true =>
      simp only [d116855, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d116929 q = 0) : d118770 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116929, d118770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d116929, d118770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116856 q = 0) : d118717 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116856, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116856, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116930 q = 0) : d118771 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d116930, d118771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116930, d118771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116931 q = 0) : d118772 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d116931, d118772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116931, d118772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117355 q = 0) : d119106 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117355, d119106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117355, d119106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro8950 (p : Pattern) (selected : d117364 p = 0) : d119115 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117343 q = 0) : d119094 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117343, d119094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8947 q selected
    | true =>
      simp only [d117343, d119094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8895 q selected
  have h2 (q : Pattern) (selected : d117344 q = 0) : d119095 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117344, d119095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117344, d119095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117345 q = 0) : d119096 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117345, d119096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117345, d119096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117351 q = 0) : d119102 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117351, d119102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8895 q selected
    | true =>
      simp only [d117351, d119102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8948 q selected
  have h5 (q : Pattern) (selected : d117352 q = 0) : d119103 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117352, d119103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117352, d119103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117353 q = 0) : d119104 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117353, d119104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117353, d119104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117354 q = 0) : d119105 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117354, d119105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117354, d119105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117356 q = 0) : d119107 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117356, d119107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8895 q selected
    | true =>
      simp only [d117356, d119107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8949 q selected
  have h9 (q : Pattern) (selected : d117357 q = 0) : d119108 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117357, d119108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117357, d119108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117358 q = 0) : d119109 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117358, d119109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117358, d119109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d117359 q = 0) : d119110 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117359, d119110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8949 q selected
    | true =>
      simp only [d117359, d119110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d117360 q = 0) : d119111 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117360, d119111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117360, d119111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d117361 q = 0) : d119112 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117361, d119112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117361, d119112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d117362 q = 0) : d119113 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117362, d119113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d117362, d119113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d117363 q = 0) : d119114 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117363, d119114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117363, d119114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d117364 q = 0) : d119115 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117364, d119115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d117364, d119115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro8951 (p : Pattern) (selected : d117369 p = 0) : d119120 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117356 q = 0) : d119107 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117356, d119107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8895 q selected
    | true =>
      simp only [d117356, d119107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8949 q selected
  have h2 (q : Pattern) (selected : d117357 q = 0) : d119108 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117357, d119108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117357, d119108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117358 q = 0) : d119109 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117358, d119109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117358, d119109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117359 q = 0) : d119110 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117359, d119110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8949 q selected
    | true =>
      simp only [d117359, d119110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117360 q = 0) : d119111 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117360, d119111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117360, d119111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117361 q = 0) : d119112 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117361, d119112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117361, d119112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117362 q = 0) : d119113 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117362, d119113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117362, d119113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117367 q = 0) : d119118 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117367, d119118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117367, d119118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117368 q = 0) : d119119 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117368, d119119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117368, d119119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117369 q = 0) : d119120 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117369, d119120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117369, d119120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro8952 (p : Pattern) (selected : d117375 p = 0) : d119126 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117365 q = 0) : d119116 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117365, d119116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8950 q selected
    | true =>
      simp only [d117365, d119116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117366 q = 0) : d119117 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117366, d119117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117366, d119117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117370 q = 0) : d119121 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117370, d119121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8951 q selected
    | true =>
      simp only [d117370, d119121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117371 q = 0) : d119122 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117371, d119122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117371, d119122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117372 q = 0) : d119123 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117372, d119123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117372, d119123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117373 q = 0) : d119124 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117373, d119124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117373, d119124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117374 q = 0) : d119125 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117374, d119125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117374, d119125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117375 q = 0) : d119126 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117375, d119126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117375, d119126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8953 (p : Pattern) (selected : d117377 p = 0) : d119128 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117359 q = 0) : d119110 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117359, d119110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8949 q selected
    | true =>
      simp only [d117359, d119110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117360 q = 0) : d119111 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117360, d119111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117360, d119111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117361 q = 0) : d119112 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117361, d119112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117361, d119112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117367 q = 0) : d119118 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117367, d119118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117367, d119118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117376 q = 0) : d119127 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117376, d119127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117376, d119127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117377 q = 0) : d119128 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117377, d119128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117377, d119128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8954 (p : Pattern) (selected : d117383 p = 0) : d119134 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117370 q = 0) : d119121 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117370, d119121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8951 q selected
    | true =>
      simp only [d117370, d119121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117371 q = 0) : d119122 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117371, d119122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117371, d119122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117378 q = 0) : d119129 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117378, d119129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8953 q selected
    | true =>
      simp only [d117378, d119129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117379 q = 0) : d119130 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117379, d119130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117379, d119130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117380 q = 0) : d119131 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117380, d119131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117380, d119131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117381 q = 0) : d119132 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117381, d119132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117381, d119132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117382 q = 0) : d119133 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117382, d119133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117382, d119133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117383 q = 0) : d119134 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117383, d119134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117383, d119134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8955 (p : Pattern) (selected : d117389 p = 0) : d118899 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117385 q = 0) : d118895 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117385, d118895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117385, d118895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8925 q selected
  have h2 (q : Pattern) (selected : d117245 q = 0) : d118831 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117245, d118831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8925 q selected
    | true =>
      simp only [d117245, d118831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117386 q = 0) : d118896 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117386, d118896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117386, d118896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117246 q = 0) : d118832 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117246, d118832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117246, d118832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117387 q = 0) : d118897 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117387, d118897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117387, d118897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117388 q = 0) : d118898 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117388, d118898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117388, d118898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117110 q = 0) : d118769 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117110, d118769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117110, d118769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8880 q selected
  have h8 (q : Pattern) (selected : d117026 q = 0) : d118716 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117026, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8880 q selected
    | true =>
      simp only [d117026, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117111 q = 0) : d118770 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117111, d118770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117111, d118770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117027 q = 0) : d118717 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117027, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117027, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d117112 q = 0) : d118771 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117112, d118771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117112, d118771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d117113 q = 0) : d118772 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117113, d118772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d117113, d118772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d117389 q = 0) : d118899 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117389, d118899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117389, d118899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro8956 (p : Pattern) (selected : d117390 p = 0) : d119106 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117110 q = 0) : d118769 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117110, d118769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117110, d118769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8880 q selected
  have h2 (q : Pattern) (selected : d117026 q = 0) : d118716 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117026, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8880 q selected
    | true =>
      simp only [d117026, d118716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117111 q = 0) : d118770 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117111, d118770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117111, d118770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117027 q = 0) : d118717 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117027, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117027, d118717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117112 q = 0) : d118771 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117112, d118771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117112, d118771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117113 q = 0) : d118772 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117113, d118772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117113, d118772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117390 q = 0) : d119106 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117390, d119106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117390, d119106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro8957 (p : Pattern) (selected : d117400 p = 0) : d119120 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117391 q = 0) : d119107 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117391, d119107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8955 q selected
    | true =>
      simp only [d117391, d119107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8956 q selected
  have h2 (q : Pattern) (selected : d117392 q = 0) : d119108 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117392, d119108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117392, d119108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117393 q = 0) : d119109 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117393, d119109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117393, d119109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117394 q = 0) : d119110 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117394, d119110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8956 q selected
    | true =>
      simp only [d117394, d119110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117395 q = 0) : d119111 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117395, d119111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117395, d119111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117396 q = 0) : d119112 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117396, d119112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117396, d119112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117397 q = 0) : d119113 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117397, d119113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117397, d119113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117398 q = 0) : d119118 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117398, d119118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117398, d119118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117399 q = 0) : d119119 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117399, d119119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117399, d119119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117400 q = 0) : d119120 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117400, d119120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117400, d119120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro8958 (p : Pattern) (selected : d117404 p = 0) : d119128 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117394 q = 0) : d119110 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117394, d119110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8956 q selected
    | true =>
      simp only [d117394, d119110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117395 q = 0) : d119111 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117395, d119111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117395, d119111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117396 q = 0) : d119112 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117396, d119112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117396, d119112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117398 q = 0) : d119118 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117398, d119118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117398, d119118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117403 q = 0) : d119127 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117403, d119127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117403, d119127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117404 q = 0) : d119128 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117404, d119128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117404, d119128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8959 (p : Pattern) (selected : d117410 p = 0) : d119134 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117401 q = 0) : d119121 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117401, d119121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8957 q selected
    | true =>
      simp only [d117401, d119121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117402 q = 0) : d119122 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117402, d119122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117402, d119122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117405 q = 0) : d119129 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117405, d119129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8958 q selected
    | true =>
      simp only [d117405, d119129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117406 q = 0) : d119130 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117406, d119130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117406, d119130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117407 q = 0) : d119131 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117407, d119131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117407, d119131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117408 q = 0) : d119132 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117408, d119132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117408, d119132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117409 q = 0) : d119133 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117409, d119133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117409, d119133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117410 q = 0) : d119134 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117410, d119134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117410, d119134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8960 (p : Pattern) (selected : d117414 p = 0) : d119139 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117405 q = 0) : d119129 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117405, d119129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8958 q selected
    | true =>
      simp only [d117405, d119129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117406 q = 0) : d119130 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117406, d119130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117406, d119130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117411 q = 0) : d119136 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117411, d119136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117411, d119136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117412 q = 0) : d119137 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117412, d119137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117412, d119137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117413 q = 0) : d119138 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117413, d119138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117413, d119138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117414 q = 0) : d119139 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117414, d119139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117414, d119139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8961 (p : Pattern) (selected : d117420 p = 0) : d119145 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117370 q = 0) : d119121 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117370, d119121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8951 q selected
    | true =>
      simp only [d117370, d119121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117371 q = 0) : d119122 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117371, d119122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117371, d119122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117417 q = 0) : d119142 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117417, d119142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117417, d119142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117418 q = 0) : d119143 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117418, d119143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117418, d119143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117419 q = 0) : d119144 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117419, d119144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117419, d119144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117420 q = 0) : d119145 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117420, d119145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117420, d119145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8962 (p : Pattern) (selected : d117426 p = 0) : d119151 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117384 q = 0) : d119135 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117384, d119135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8952 q selected
    | true =>
      simp only [d117384, d119135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8954 q selected
  have h2 (q : Pattern) (selected : d117415 q = 0) : d119140 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117415, d119140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8959 q selected
    | true =>
      simp only [d117415, d119140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8960 q selected
  have h3 (q : Pattern) (selected : d117416 q = 0) : d119141 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117416, d119141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117416, d119141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117421 q = 0) : d119146 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117421, d119146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8961 q selected
    | true =>
      simp only [d117421, d119146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117422 q = 0) : d119147 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117422, d119147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117422, d119147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117423 q = 0) : d119148 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117423, d119148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117423, d119148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117424 q = 0) : d119149 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117424, d119149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117424, d119149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117425 q = 0) : d119150 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117425, d119150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117425, d119150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d117426 q = 0) : d119151 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117426, d119151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117426, d119151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro8963 (p : Pattern) (selected : d117431 p = 0) : d119139 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117378 q = 0) : d119129 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117378, d119129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8953 q selected
    | true =>
      simp only [d117378, d119129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117379 q = 0) : d119130 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117379, d119130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117379, d119130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117428 q = 0) : d119136 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117428, d119136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117428, d119136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117429 q = 0) : d119137 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117429, d119137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117429, d119137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117430 q = 0) : d119138 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117430, d119138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117430, d119138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117431 q = 0) : d119139 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117431, d119139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117431, d119139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8964 (p : Pattern) (selected : d117437 p = 0) : d119158 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117432 q = 0) : d119153 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117432, d119153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8963 q selected
    | true =>
      simp only [d117432, d119153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117433 q = 0) : d119154 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117433, d119154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117433, d119154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117434 q = 0) : d119155 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117434, d119155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117434, d119155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117435 q = 0) : d119156 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117435, d119156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117435, d119156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117436 q = 0) : d119157 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117436, d119157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117436, d119157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117437 q = 0) : d119158 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117437, d119158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117437, d119158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro8965 (p : Pattern) (selected : d117443 p = 0) : d119164 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117189 q = 0) : d118974 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d117189, d118974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117189, d118974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8911 q selected
  have h2 (q : Pattern) (selected : d117190 q = 0) : d118975 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d117190, d118975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117190, d118975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117199 q = 0) : d118984 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d117199, d118984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8911 q selected
    | true =>
      simp only [d117199, d118984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8914 q selected
  have h4 (q : Pattern) (selected : d117200 q = 0) : d118985 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d117200, d118985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117200, d118985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117201 q = 0) : d118986 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d117201, d118986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117201, d118986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117311 q = 0) : d119062 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d117311, d119062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8933 q selected
    | true =>
      simp only [d117311, d119062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8942 q selected
  have h7 (q : Pattern) (selected : d117324 q = 0) : d119075 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d117324, d119075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8943 q selected
    | true =>
      simp only [d117324, d119075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8944 q selected
  have h8 (q : Pattern) (selected : d117325 q = 0) : d119076 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d117325, d119076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117325, d119076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d117326 q = 0) : d119077 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d117326, d119077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117326, d119077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d117327 q = 0) : d119078 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d117327, d119078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117327, d119078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d117331 q = 0) : d119082 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d117331, d119082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117331, d119082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8945 q selected
  have h12 (q : Pattern) (selected : d117333 q = 0) : d119084 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d117333, d119084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117333, d119084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8946 q selected
  have h13 (q : Pattern) (selected : d117334 q = 0) : d119085 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d117334, d119085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d117334, d119085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d117335 q = 0) : d119086 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d117335, d119086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d117335, d119086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d117336 q = 0) : d119087 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d117336, d119087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d117336, d119087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d117337 q = 0) : d119088 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d117337, d119088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d117337, d119088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d117427 q = 0) : d119152 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d117427, d119152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117427, d119152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8962 q selected
  have h18 (q : Pattern) (selected : d117438 q = 0) : d119159 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d117438, d119159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117438, d119159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8964 q selected
  have h19 (q : Pattern) (selected : d117439 q = 0) : d119160 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d117439, d119160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d117439, d119160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d117440 q = 0) : d119161 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d117440, d119161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d117440, d119161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d117441 q = 0) : d119162 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d117441, d119162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d117441, d119162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d117442 q = 0) : d119163 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d117442, d119163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d117442, d119163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d117443 q = 0) : d119164 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d117443, d119164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d117443, d119164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro8966 (p : Pattern) (selected : d117449 p = 0) : d119170 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117444 q = 0) : d119165 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d117444, d119165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117444, d119165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8965 q selected
  have h2 (q : Pattern) (selected : d117445 q = 0) : d119166 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d117445, d119166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117445, d119166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117446 q = 0) : d119167 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d117446, d119167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117446, d119167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117447 q = 0) : d119168 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d117447, d119168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117447, d119168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117448 q = 0) : d119169 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d117448, d119169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117448, d119169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117449 q = 0) : d119170 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d117449, d119170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117449, d119170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro8967 (p : Pattern) (selected : d1098 p = 0) : d52679 p = 1 := by
  have h0 (q : Pattern) (selected : d1088 q = 0) : d52669 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1088, d52669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro275 q selected
    | true =>
      simp only [d1088, d52669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro384 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1089 q = 0) : d52670 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1089, d52670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1089, d52670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1094 q = 0) : d52675 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1094, d52675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro234 q selected
    | true =>
      simp only [d1094, d52675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro385 q selected
  have h4 (q : Pattern) (selected : d1095 q = 0) : d52676 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1095, d52676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1095, d52676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d1096 q = 0) : d52677 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1096, d52677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1096, d52677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d537 q = 0) : d52284 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d537, d52284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro276 q selected
    | true =>
      simp only [d537, d52284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d538 q = 0) : d52285 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d538, d52285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d538, d52285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d133 q = 0) : d51984 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro204 q selected
    | true =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d134 q = 0) : d51985 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d539 q = 0) : d52286 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d539, d52286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d539, d52286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d1097 q = 0) : d52678 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1097, d52678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1097, d52678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d1098 q = 0) : d52679 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1098, d52679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d1098, d52679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h12 p selected
theorem eqIntro8968 (p : Pattern) (selected : d1108 p = 0) : d52689 p = 1 := by
  have h0 (q : Pattern) (selected : d1094 q = 0) : d52675 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1094, d52675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro234 q selected
    | true =>
      simp only [d1094, d52675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro385 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1095 q = 0) : d52676 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1095, d52676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1095, d52676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1104 q = 0) : d52685 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1104, d52685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro204 q selected
    | true =>
      simp only [d1104, d52685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
  have h4 (q : Pattern) (selected : d1105 q = 0) : d52686 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1105, d52686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1105, d52686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d1106 q = 0) : d52687 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1106, d52687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1106, d52687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133 q = 0) : d51984 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro204 q selected
    | true =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d134 q = 0) : d51985 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d19 q = 0) : d51871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d20 q = 0) : d51872 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d135 q = 0) : d51986 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d51986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135, d51986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d1107 q = 0) : d52688 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1107, d52688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1107, d52688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d1108 q = 0) : d52689 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1108, d52689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d1108, d52689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h12 p selected
theorem eqIntro8969 (p : Pattern) (selected : d117460 p = 0) : d119181 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117452 q = 0) : d119173 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117452, d119173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8967 q selected
    | true =>
      simp only [d117452, d119173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117453 q = 0) : d119174 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117453, d119174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117453, d119174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117454 q = 0) : d119175 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117454, d119175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117454, d119175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117455 q = 0) : d119176 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117455, d119176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117455, d119176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117456 q = 0) : d119177 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117456, d119177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8968 q selected
    | true =>
      simp only [d117456, d119177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117457 q = 0) : d119178 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117457, d119178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117457, d119178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117458 q = 0) : d119179 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117458, d119179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117458, d119179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117459 q = 0) : d119180 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117459, d119180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117459, d119180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117460 q = 0) : d119181 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117460, d119181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117460, d119181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro8970 (p : Pattern) (selected : d1119 p = 0) : d52700 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1115 q = 0) : d52696 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
  have h2 (q : Pattern) (selected : d1116 q = 0) : d52697 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1116, d52697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1116, d52697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
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
  have h5 (q : Pattern) (selected : d1117 q = 0) : d52698 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1117, d52698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1117, d52698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d21 q = 0) : d51873 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1118 q = 0) : d52699 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1118, d52699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1118, d52699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d1119 q = 0) : d52700 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1119, d52700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1119, d52700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8971 (p : Pattern) (selected : d117465 p = 0) : d119186 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117456 q = 0) : d119177 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117456, d119177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8968 q selected
    | true =>
      simp only [d117456, d119177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117457 q = 0) : d119178 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117457, d119178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117457, d119178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117458 q = 0) : d119179 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117458, d119179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117458, d119179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117459 q = 0) : d119180 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117459, d119180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117459, d119180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117461 q = 0) : d119182 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117461, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8970 q selected
    | true =>
      simp only [d117461, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117462 q = 0) : d119183 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117462, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117462, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117463 q = 0) : d119184 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117463, d119184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117463, d119184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117464 q = 0) : d119185 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117464, d119185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117464, d119185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117465 q = 0) : d119186 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117465, d119186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117465, d119186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro8972 (p : Pattern) (selected : d117469 p = 0) : d119190 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117461 q = 0) : d119182 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117461, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8970 q selected
    | true =>
      simp only [d117461, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117462 q = 0) : d119183 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117462, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117462, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117463 q = 0) : d119184 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117463, d119184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117463, d119184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117464 q = 0) : d119185 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117464, d119185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117464, d119185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117469 q = 0) : d119190 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117469, d119190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117469, d119190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro8973 (p : Pattern) (selected : d117476 p = 0) : d119197 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117466 q = 0) : d119187 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117466, d119187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8969 q selected
    | true =>
      simp only [d117466, d119187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8971 q selected
  have h2 (q : Pattern) (selected : d117467 q = 0) : d119188 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117467, d119188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117467, d119188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117468 q = 0) : d119189 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117468, d119189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117468, d119189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117470 q = 0) : d119191 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117470, d119191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8971 q selected
    | true =>
      simp only [d117470, d119191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8972 q selected
  have h5 (q : Pattern) (selected : d117471 q = 0) : d119192 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117471, d119192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117471, d119192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117472 q = 0) : d119193 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117472, d119193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117472, d119193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117473 q = 0) : d119194 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117473, d119194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117473, d119194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117474 q = 0) : d119195 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117474, d119195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117474, d119195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117475 q = 0) : d119196 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117475, d119196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117475, d119196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117476 q = 0) : d119197 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117476, d119197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117476, d119197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro8974 (p : Pattern) (selected : d117480 p = 0) : d119201 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117470 q = 0) : d119191 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117470, d119191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8971 q selected
    | true =>
      simp only [d117470, d119191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8972 q selected
  have h2 (q : Pattern) (selected : d117471 q = 0) : d119192 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117471, d119192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117471, d119192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117472 q = 0) : d119193 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117472, d119193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117472, d119193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117474 q = 0) : d119195 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117474, d119195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117474, d119195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117479 q = 0) : d119200 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117479, d119200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117479, d119200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117480 q = 0) : d119201 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117480, d119201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117480, d119201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8975 (p : Pattern) (selected : d117486 p = 0) : d119207 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117477 q = 0) : d119198 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117477, d119198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8973 q selected
    | true =>
      simp only [d117477, d119198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117478 q = 0) : d119199 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117478, d119199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117478, d119199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117481 q = 0) : d119202 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117481, d119202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8974 q selected
    | true =>
      simp only [d117481, d119202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117482 q = 0) : d119203 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117482, d119203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117482, d119203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117483 q = 0) : d119204 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117483, d119204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117483, d119204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117484 q = 0) : d119205 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117484, d119205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117484, d119205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117485 q = 0) : d119206 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117485, d119206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117485, d119206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117486 q = 0) : d119207 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117486, d119207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117486, d119207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro8976 (p : Pattern) (selected : d117490 p = 0) : d119211 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117481 q = 0) : d119202 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117481, d119202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8974 q selected
    | true =>
      simp only [d117481, d119202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117482 q = 0) : d119203 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117482, d119203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117482, d119203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117487 q = 0) : d119208 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117487, d119208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117487, d119208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117488 q = 0) : d119209 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117488, d119209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117488, d119209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117489 q = 0) : d119210 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117489, d119210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117489, d119210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117490 q = 0) : d119211 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117490, d119211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117490, d119211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro8977 (p : Pattern) (selected : d117496 p = 0) : d119217 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117491 q = 0) : d119212 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117491, d119212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8975 q selected
    | true =>
      simp only [d117491, d119212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8976 q selected
  have h2 (q : Pattern) (selected : d117492 q = 0) : d119213 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117492, d119213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117492, d119213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117493 q = 0) : d119214 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117493, d119214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117493, d119214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117494 q = 0) : d119215 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117494, d119215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117494, d119215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117495 q = 0) : d119216 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117495, d119216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117495, d119216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117496 q = 0) : d119217 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117496, d119217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117496, d119217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro8978 (p : Pattern) (selected : d117499 p = 0) : d119220 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117477 q = 0) : d119198 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117477, d119198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8973 q selected
    | true =>
      simp only [d117477, d119198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117478 q = 0) : d119199 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117478, d119199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117478, d119199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117481 q = 0) : d119202 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117481, d119202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8974 q selected
    | true =>
      simp only [d117481, d119202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117482 q = 0) : d119203 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117482, d119203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117482, d119203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117483 q = 0) : d119204 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117483, d119204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117483, d119204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117484 q = 0) : d119205 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117484, d119205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117484, d119205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117485 q = 0) : d119206 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117485, d119206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117485, d119206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117499 q = 0) : d119220 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117499, d119220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117499, d119220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8979 (p : Pattern) (selected : d117500 p = 0) : d119221 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117481 q = 0) : d119202 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117481, d119202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8974 q selected
    | true =>
      simp only [d117481, d119202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117482 q = 0) : d119203 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117482, d119203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117482, d119203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117487 q = 0) : d119208 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117487, d119208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117487, d119208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117488 q = 0) : d119209 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117488, d119209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117488, d119209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117489 q = 0) : d119210 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117489, d119210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117489, d119210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117500 q = 0) : d119221 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117500, d119221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117500, d119221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8980 (p : Pattern) (selected : d117506 p = 0) : d119227 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117491 q = 0) : d119212 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117491, d119212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8975 q selected
    | true =>
      simp only [d117491, d119212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8976 q selected
  have h2 (q : Pattern) (selected : d117492 q = 0) : d119213 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117492, d119213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117492, d119213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117493 q = 0) : d119214 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117493, d119214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117493, d119214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117494 q = 0) : d119215 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117494, d119215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117494, d119215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117495 q = 0) : d119216 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117495, d119216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117495, d119216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117501 q = 0) : d119222 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117501, d119222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8978 q selected
    | true =>
      simp only [d117501, d119222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8979 q selected
  have h7 (q : Pattern) (selected : d117502 q = 0) : d119223 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117502, d119223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117502, d119223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117503 q = 0) : d119224 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117503, d119224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117503, d119224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117504 q = 0) : d119225 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117504, d119225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117504, d119225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117505 q = 0) : d119226 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117505, d119226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117505, d119226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d117506 q = 0) : d119227 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117506, d119227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117506, d119227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro8981 (p : Pattern) (selected : d117511 p = 0) : d119232 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117477 q = 0) : d119198 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117477, d119198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8973 q selected
    | true =>
      simp only [d117477, d119198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117478 q = 0) : d119199 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117478, d119199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117478, d119199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117481 q = 0) : d119202 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117481, d119202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8974 q selected
    | true =>
      simp only [d117481, d119202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117482 q = 0) : d119203 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117482, d119203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117482, d119203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117483 q = 0) : d119204 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117483, d119204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117483, d119204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117484 q = 0) : d119205 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117484, d119205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117484, d119205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117510 q = 0) : d119231 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117510, d119231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117510, d119231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117511 q = 0) : d119232 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117511, d119232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117511, d119232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro8982 (p : Pattern) (selected : d117513 p = 0) : d119234 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117481 q = 0) : d119202 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117481, d119202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8974 q selected
    | true =>
      simp only [d117481, d119202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117482 q = 0) : d119203 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117482, d119203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117482, d119203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117487 q = 0) : d119208 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117487, d119208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117487, d119208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117488 q = 0) : d119209 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117488, d119209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117488, d119209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117512 q = 0) : d119233 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117512, d119233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117512, d119233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117513 q = 0) : d119234 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117513, d119234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117513, d119234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro8983 (p : Pattern) (selected : d117520 p = 0) : d119241 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117477 q = 0) : d119198 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117477, d119198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8973 q selected
    | true =>
      simp only [d117477, d119198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117478 q = 0) : d119199 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117478, d119199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117478, d119199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117481 q = 0) : d119202 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117481, d119202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8974 q selected
    | true =>
      simp only [d117481, d119202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117482 q = 0) : d119203 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117482, d119203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117482, d119203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117483 q = 0) : d119204 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117483, d119204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117483, d119204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117518 q = 0) : d119239 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117518, d119239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117518, d119239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117519 q = 0) : d119240 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117519, d119240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117519, d119240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117520 q = 0) : d119241 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117520, d119241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117520, d119241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro8984 (p : Pattern) (selected : d117523 p = 0) : d119244 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117481 q = 0) : d119202 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117481, d119202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8974 q selected
    | true =>
      simp only [d117481, d119202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117482 q = 0) : d119203 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117482, d119203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117482, d119203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117487 q = 0) : d119208 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117487, d119208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117487, d119208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117521 q = 0) : d119242 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117521, d119242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117521, d119242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117522 q = 0) : d119243 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117522, d119243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117522, d119243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117523 q = 0) : d119244 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117523, d119244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117523, d119244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro8985 (p : Pattern) (selected : d1092 p = 0) : d52673 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d822 q = 0) : d52499 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d822, d52499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro333 q selected
    | true =>
      simp only [d822, d52499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d823 q = 0) : d52500 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d823, d52500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d823, d52500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1088 q = 0) : d52669 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1088, d52669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro275 q selected
    | true =>
      simp only [d1088, d52669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro384 q selected
  have h4 (q : Pattern) (selected : d1089 q = 0) : d52670 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1089, d52670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1089, d52670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1090 q = 0) : d52671 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1090, d52671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1090, d52671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d828 q = 0) : d52505 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d828, d52505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro334 q selected
    | true =>
      simp only [d828, d52505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d829 q = 0) : d52506 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d829, d52506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d829, d52506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d537 q = 0) : d52284 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d537, d52284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro276 q selected
    | true =>
      simp only [d537, d52284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d538 q = 0) : d52285 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d538, d52285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d538, d52285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d830 q = 0) : d52507 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d830, d52507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d830, d52507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d1091 q = 0) : d52672 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1091, d52672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1091, d52672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d1092 q = 0) : d52673 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1092, d52673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d1092, d52673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h12 p selected
theorem eqIntro8986 (p : Pattern) (selected : d117531 p = 0) : d119252 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117527 q = 0) : d119248 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117527, d119248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8985 q selected
    | true =>
      simp only [d117527, d119248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117528 q = 0) : d119249 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117528, d119249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117528, d119249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117529 q = 0) : d119250 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117529, d119250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117529, d119250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117530 q = 0) : d119251 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117530, d119251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117530, d119251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117452 q = 0) : d119173 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117452, d119173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8967 q selected
    | true =>
      simp only [d117452, d119173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117453 q = 0) : d119174 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117453, d119174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117453, d119174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117454 q = 0) : d119175 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117454, d119175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117454, d119175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117455 q = 0) : d119176 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117455, d119176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117455, d119176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117531 q = 0) : d119252 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117531, d119252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117531, d119252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro8987 (p : Pattern) (selected : d9776 p = 0) : d101297 p = 1 := by
  have h0 (q : Pattern) (selected : d9772 q = 0) : d101293 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9772, d101293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6640 q selected
    | true =>
      simp only [d9772, d101293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6671 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d9773 q = 0) : d101294 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9773, d101294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9773, d101294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d9452 q = 0) : d101067 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9452, d101067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2798 q selected
    | true =>
      simp only [d9452, d101067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d9453 q = 0) : d101068 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d101068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9453, d101068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d9774 q = 0) : d101295 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9774, d101295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9774, d101295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9775 q = 0) : d101296 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9775, d101296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9775, d101296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d9776 q = 0) : d101297 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9776, d101297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9776, d101297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h7 p selected
theorem eqIntro8988 (p : Pattern) (selected : d117539 p = 0) : d119260 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117535 q = 0) : d119256 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117535, d119256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8987 q selected
    | true =>
      simp only [d117535, d119256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117536 q = 0) : d119257 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117536, d119257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117536, d119257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117537 q = 0) : d119258 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117537, d119258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117537, d119258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117538 q = 0) : d119259 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117538, d119259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117538, d119259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117539 q = 0) : d119260 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117539, d119260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117539, d119260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro8989 (p : Pattern) (selected : d117545 p = 0) : d119266 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117532 q = 0) : d119253 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117532, d119253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8986 q selected
    | true =>
      simp only [d117532, d119253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8969 q selected
  have h2 (q : Pattern) (selected : d117533 q = 0) : d119254 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117533, d119254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117533, d119254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117534 q = 0) : d119255 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117534, d119255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117534, d119255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117540 q = 0) : d119261 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117540, d119261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8969 q selected
    | true =>
      simp only [d117540, d119261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8988 q selected
  have h5 (q : Pattern) (selected : d117541 q = 0) : d119262 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117541, d119262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117541, d119262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117542 q = 0) : d119263 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117542, d119263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117542, d119263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117543 q = 0) : d119264 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117543, d119264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117543, d119264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117466 q = 0) : d119187 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117466, d119187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8969 q selected
    | true =>
      simp only [d117466, d119187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8971 q selected
  have h9 (q : Pattern) (selected : d117467 q = 0) : d119188 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117467, d119188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117467, d119188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117468 q = 0) : d119189 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117468, d119189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117468, d119189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d117470 q = 0) : d119191 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117470, d119191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8971 q selected
    | true =>
      simp only [d117470, d119191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8972 q selected
  have h12 (q : Pattern) (selected : d117471 q = 0) : d119192 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117471, d119192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117471, d119192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d117472 q = 0) : d119193 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117472, d119193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117472, d119193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d117473 q = 0) : d119194 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117473, d119194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d117473, d119194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d117544 q = 0) : d119265 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117544, d119265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117544, d119265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d117545 q = 0) : d119266 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117545, d119266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d117545, d119266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro8990 (p : Pattern) (selected : d117551 p = 0) : d119272 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117546 q = 0) : d119267 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117546, d119267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8989 q selected
    | true =>
      simp only [d117546, d119267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117547 q = 0) : d119268 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117547, d119268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117547, d119268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117477 q = 0) : d119198 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117477, d119198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8973 q selected
    | true =>
      simp only [d117477, d119198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117478 q = 0) : d119199 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117478, d119199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117478, d119199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117548 q = 0) : d119269 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117548, d119269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117548, d119269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117549 q = 0) : d119270 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117549, d119270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117549, d119270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117550 q = 0) : d119271 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117550, d119271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117550, d119271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117551 q = 0) : d119272 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117551, d119272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117551, d119272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro8991 (p : Pattern) (selected : d1253 p = 0) : d52679 p = 1 := by
  have h0 (q : Pattern) (selected : d1237 q = 0) : d52669 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1237, d52669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro339 q selected
    | true =>
      simp only [d1237, d52669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro412 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1238 q = 0) : d52670 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1238, d52670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1238, d52670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1249 q = 0) : d52675 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1249, d52675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro281 q selected
    | true =>
      simp only [d1249, d52675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro414 q selected
  have h4 (q : Pattern) (selected : d1250 q = 0) : d52676 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1250, d52676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1250, d52676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d1251 q = 0) : d52677 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1251, d52677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1251, d52677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d862 q = 0) : d52284 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d862, d52284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro340 q selected
    | true =>
      simp only [d862, d52284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d863 q = 0) : d52285 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d863, d52285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d863, d52285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d344 q = 0) : d51984 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d344, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro239 q selected
    | true =>
      simp only [d344, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d345 q = 0) : d51985 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d345, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d345, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d864 q = 0) : d52286 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d864, d52286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d864, d52286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d1252 q = 0) : d52678 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1252, d52678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1252, d52678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d1253 q = 0) : d52679 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1253, d52679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d1253, d52679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h12 p selected
theorem eqIntro8992 (p : Pattern) (selected : d1263 p = 0) : d52689 p = 1 := by
  have h0 (q : Pattern) (selected : d1249 q = 0) : d52675 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1249, d52675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro281 q selected
    | true =>
      simp only [d1249, d52675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro414 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1250 q = 0) : d52676 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1250, d52676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1250, d52676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1259 q = 0) : d52685 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1259, d52685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro239 q selected
    | true =>
      simp only [d1259, d52685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
  have h4 (q : Pattern) (selected : d1260 q = 0) : d52686 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1260, d52686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1260, d52686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d1261 q = 0) : d52687 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1261, d52687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1261, d52687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d344 q = 0) : d51984 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d344, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro239 q selected
    | true =>
      simp only [d344, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d345 q = 0) : d51985 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d345, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d345, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d164 q = 0) : d51871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
    | true =>
      simp only [d164, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d165 q = 0) : d51872 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d165, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d165, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d346 q = 0) : d51986 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d346, d51986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d346, d51986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d1262 q = 0) : d52688 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1262, d52688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1262, d52688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d1263 q = 0) : d52689 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1263, d52689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d1263, d52689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h12 p selected
theorem eqIntro8993 (p : Pattern) (selected : d117561 p = 0) : d119181 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117553 q = 0) : d119173 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117553, d119173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8991 q selected
    | true =>
      simp only [d117553, d119173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117554 q = 0) : d119174 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117554, d119174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117554, d119174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117555 q = 0) : d119175 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117555, d119175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117555, d119175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117556 q = 0) : d119176 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117556, d119176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117556, d119176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117557 q = 0) : d119177 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117557, d119177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8992 q selected
    | true =>
      simp only [d117557, d119177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117558 q = 0) : d119178 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117558, d119178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117558, d119178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117559 q = 0) : d119179 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117559, d119179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117559, d119179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117560 q = 0) : d119180 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117560, d119180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117560, d119180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117561 q = 0) : d119181 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117561, d119181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117561, d119181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro8994 (p : Pattern) (selected : d1274 p = 0) : d52700 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1270 q = 0) : d52696 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1270, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1270, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
  have h2 (q : Pattern) (selected : d1271 q = 0) : d52697 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1271, d52697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1271, d52697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
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
  have h5 (q : Pattern) (selected : d1272 q = 0) : d52698 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1272, d52698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1272, d52698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166 q = 0) : d51873 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d166, d51873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166, d51873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1273 q = 0) : d52699 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1273, d52699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1273, d52699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d1274 q = 0) : d52700 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1274, d52700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1274, d52700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro8995 (p : Pattern) (selected : d117566 p = 0) : d119186 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117557 q = 0) : d119177 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117557, d119177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8992 q selected
    | true =>
      simp only [d117557, d119177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117558 q = 0) : d119178 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117558, d119178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117558, d119178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117559 q = 0) : d119179 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117559, d119179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117559, d119179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117560 q = 0) : d119180 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117560, d119180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117560, d119180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117562 q = 0) : d119182 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117562, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8994 q selected
    | true =>
      simp only [d117562, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117563 q = 0) : d119183 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117563, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117563, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117564 q = 0) : d119184 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117564, d119184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117564, d119184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117565 q = 0) : d119185 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117565, d119185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117565, d119185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117566 q = 0) : d119186 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117566, d119186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117566, d119186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro8996 (p : Pattern) (selected : d117570 p = 0) : d119190 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117562 q = 0) : d119182 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117562, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8994 q selected
    | true =>
      simp only [d117562, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117563 q = 0) : d119183 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117563, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117563, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117564 q = 0) : d119184 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117564, d119184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117564, d119184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117565 q = 0) : d119185 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117565, d119185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117565, d119185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117570 q = 0) : d119190 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117570, d119190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117570, d119190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro8997 (p : Pattern) (selected : d117577 p = 0) : d119197 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117567 q = 0) : d119187 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117567, d119187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8993 q selected
    | true =>
      simp only [d117567, d119187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8995 q selected
  have h2 (q : Pattern) (selected : d117568 q = 0) : d119188 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117568, d119188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117568, d119188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117569 q = 0) : d119189 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117569, d119189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117569, d119189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117571 q = 0) : d119191 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117571, d119191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8995 q selected
    | true =>
      simp only [d117571, d119191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8996 q selected
  have h5 (q : Pattern) (selected : d117572 q = 0) : d119192 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117572, d119192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117572, d119192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117573 q = 0) : d119193 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117573, d119193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117573, d119193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117574 q = 0) : d119194 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117574, d119194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117574, d119194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117575 q = 0) : d119195 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117575, d119195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117575, d119195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117576 q = 0) : d119196 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117576, d119196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117576, d119196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117577 q = 0) : d119197 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117577, d119197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117577, d119197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro8998 (p : Pattern) (selected : d117581 p = 0) : d119201 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117571 q = 0) : d119191 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117571, d119191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8995 q selected
    | true =>
      simp only [d117571, d119191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8996 q selected
  have h2 (q : Pattern) (selected : d117572 q = 0) : d119192 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117572, d119192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117572, d119192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117573 q = 0) : d119193 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117573, d119193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117573, d119193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117575 q = 0) : d119195 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117575, d119195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117575, d119195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117580 q = 0) : d119200 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117580, d119200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117580, d119200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117581 q = 0) : d119201 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117581, d119201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117581, d119201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro8999 (p : Pattern) (selected : d117587 p = 0) : d119207 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117578 q = 0) : d119198 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117578, d119198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8997 q selected
    | true =>
      simp only [d117578, d119198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117579 q = 0) : d119199 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117579, d119199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117579, d119199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117582 q = 0) : d119202 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117582, d119202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8998 q selected
    | true =>
      simp only [d117582, d119202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117583 q = 0) : d119203 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117583, d119203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117583, d119203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117584 q = 0) : d119204 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117584, d119204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117584, d119204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117585 q = 0) : d119205 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117585, d119205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117585, d119205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117586 q = 0) : d119206 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117586, d119206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117586, d119206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117587 q = 0) : d119207 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117587, d119207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117587, d119207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
end NetHack.Soko22Hazard87
