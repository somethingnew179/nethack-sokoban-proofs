import NetHack.Soko22Hazard87.AndIntroBlocks0079
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro20000 (p : Pattern) (ha : d8937 p = 1) (hb : d116753 p = 1) : d120890 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d116753 q = 1) : d120856 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d120856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19988 q ha hb
    | true =>
      simp only [d8912, d120856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d116753 q = 1) : d120857 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d120857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d120857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d116753 q = 1) : d120860 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19976 q ha hb
    | true =>
      simp only [d1614, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d116753 q = 1) : d120861 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8914 q = 1) (hb : d116753 q = 1) : d120862 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, d120862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8914, d120862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8915 q = 1) (hb : d116753 q = 1) : d120863 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8915, d120863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8915, d120863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8936 q = 1) (hb : d116753 q = 1) : d120889 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8936, d120889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8936, d120889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8937 q = 1) (hb : d116753 q = 1) : d120890 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8937, d120890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8937, d120890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20001 (p : Pattern) (ha : d8944 p = 1) (hb : d116753 p = 1) : d120899 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d116753 q = 1) : d120856 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d120856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19988 q ha hb
    | true =>
      simp only [d8912, d120856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d116753 q = 1) : d120857 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d120857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d120857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d116753 q = 1) : d120860 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19976 q ha hb
    | true =>
      simp only [d1614, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d116753 q = 1) : d120861 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8914 q = 1) (hb : d116753 q = 1) : d120862 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, d120862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8914, d120862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8942 q = 1) (hb : d116753 q = 1) : d120897 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8942, d120897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8942, d120897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8943 q = 1) (hb : d116753 q = 1) : d120898 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8943, d120898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8943, d120898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8944 q = 1) (hb : d116753 q = 1) : d120899 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8944, d120899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8944, d120899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20002 (p : Pattern) (ha : d1554 p = 1) (hb : d116750 p = 1) : d10035 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1538 q = 1) : d1538 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1553 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1554 q = 1) (hb : d116750 q = 1) : d10035 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1554, d116750, d10035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1554, d116750, d10035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro20003 (p : Pattern) (ha : d1670 p = 1) (hb : d116752 p = 1) : d120906 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1669 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1555 q = 1) (hb : d116750 q = 1) : d10036 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d10036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20002 q ha hb
    | true =>
      simp only [d1555, d10036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1556 q = 1) (hb : d116750 q = 1) : d10038 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d10038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1556, d10038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1557 q = 1) (hb : d116750 q = 1) : d16859 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1557, d16859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1557, d16859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1558 q = 1) (hb : d116750 q = 1) : d16860 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1558, d16860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1558, d16860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1570 q = 1) (hb : d116750 q = 1) : d22220 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d22220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19986 q ha hb
    | true =>
      simp only [d1570, d22220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d1571 q = 1) (hb : d116750 q = 1) : d22221 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d22221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1571, d22221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1572 q = 1) (hb : d116750 q = 1) : d22222 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1572, d22222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1572, d22222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1573 q = 1) (hb : d116750 q = 1) : d22223 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1573, d22223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1573, d22223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d1574 q = 1) (hb : d116750 q = 1) : d22224 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1574, d22224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1574, d22224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1670 q = 1) (hb : d116752 q = 1) : d120906 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1670, d116752, d120906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1670, d116752, d120906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro20004 (p : Pattern) (ha : d8950 p = 1) (hb : d116753 p = 1) : d120912 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1671 q = 1) (hb : d116752 q = 1) : d120907 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1671, d120907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20003 q ha hb
    | true =>
      simp only [d1671, d120907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19987 q ha hb
  have h2 (q : Pattern) (ha : d1672 q = 1) (hb : d116752 q = 1) : d120908 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1672, d120908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1672, d120908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1673 q = 1) (hb : d116752 q = 1) : d120909 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1673, d120909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1673, d120909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8948 q = 1) (hb : d116753 q = 1) : d120910 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8948, d116753, d120910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8948, d116753, d120910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1590 q = 1) (hb : d116752 q = 1) : d120845 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1590, d120845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19987 q ha hb
    | true =>
      simp only [d1590, d120845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19974 q ha hb
  have h7 (q : Pattern) (ha : d1591 q = 1) (hb : d116752 q = 1) : d120846 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1591, d120846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1591, d120846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1592 q = 1) (hb : d116752 q = 1) : d120847 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1592, d120847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1592, d120847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7034 q = 1) (hb : d116753 q = 1) : d120848 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7034, d116753, d120848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7034, d116753, d120848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d8949 q = 1) (hb : d116753 q = 1) : d120911 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8949, d120911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8949, d120911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d8950 q = 1) (hb : d116753 q = 1) : d120912 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8950, d120912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8950, d120912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro20005 (p : Pattern) (ha : d8956 p = 1) (hb : d116753 p = 1) : d120922 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8951 q = 1) (hb : d116753 q = 1) : d120913 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8951, d120913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20004 q ha hb
    | true =>
      simp only [d8951, d120913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8952 q = 1) (hb : d116753 q = 1) : d120914 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8952, d120914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8952, d120914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7037 q = 1) (hb : d116753 q = 1) : d120917 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7037, d120917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19995 q ha hb
    | true =>
      simp only [d7037, d120917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7038 q = 1) (hb : d116753 q = 1) : d120918 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7038, d120918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7038, d120918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8953 q = 1) (hb : d116753 q = 1) : d120919 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8953, d120919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8953, d120919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8954 q = 1) (hb : d116753 q = 1) : d120920 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8954, d120920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8954, d120920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8955 q = 1) (hb : d116753 q = 1) : d120921 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8955, d120921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8955, d120921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8956 q = 1) (hb : d116753 q = 1) : d120922 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8956, d120922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8956, d120922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20006 (p : Pattern) (ha : d8976 p = 1) (hb : d116753 p = 1) : d120932 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d116753 q = 1) : d120856 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d120856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19988 q ha hb
    | true =>
      simp only [d8912, d120856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d116753 q = 1) : d120857 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d120857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d120857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8973 q = 1) (hb : d116753 q = 1) : d120929 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8973, d120929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8973, d120929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8974 q = 1) (hb : d116753 q = 1) : d120930 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8974, d120930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8974, d120930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8975 q = 1) (hb : d116753 q = 1) : d120931 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8975, d120931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8975, d120931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8976 q = 1) (hb : d116753 q = 1) : d120932 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8976, d120932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8976, d120932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20007 (p : Pattern) (ha : d94391 p = 1) (hb : d116753 p = 1) : d120938 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8938 q = 1) (hb : d116753 q = 1) : d120893 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8938, d120893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20000 q ha hb
    | true =>
      simp only [d8938, d120893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19998 q ha hb
  have h2 (q : Pattern) (ha : d8939 q = 1) (hb : d116753 q = 1) : d120894 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8939, d120894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8939, d120894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8940 q = 1) (hb : d116753 q = 1) : d120895 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8940, d120895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8940, d120895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8941 q = 1) (hb : d116753 q = 1) : d120896 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8941, d120896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8941, d120896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8945 q = 1) (hb : d116753 q = 1) : d120903 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8945, d120903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20001 q ha hb
    | true =>
      simp only [d8945, d120903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19999 q ha hb
  have h6 (q : Pattern) (ha : d8946 q = 1) (hb : d116753 q = 1) : d120904 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8946, d120904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8946, d120904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8947 q = 1) (hb : d116753 q = 1) : d120905 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8947, d120905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8947, d120905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8961 q = 1) (hb : d116753 q = 1) : d120927 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8961, d120927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20005 q ha hb
    | true =>
      simp only [d8961, d120927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19996 q ha hb
  have h9 (q : Pattern) (ha : d94387 q = 1) (hb : d116753 q = 1) : d120928 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94387, d120928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94387, d120928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8977 q = 1) (hb : d116753 q = 1) : d120933 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8977, d120933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20006 q ha hb
    | true =>
      simp only [d8977, d120933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8978 q = 1) (hb : d116753 q = 1) : d120934 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8978, d120934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8978, d120934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94388 q = 1) (hb : d116753 q = 1) : d120935 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94388, d120935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94388, d120935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94389 q = 1) (hb : d116753 q = 1) : d120936 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94389, d120936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94389, d120936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94390 q = 1) (hb : d116753 q = 1) : d120937 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94390, d120937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94390, d120937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94391 q = 1) (hb : d116753 q = 1) : d120938 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94391, d120938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94391, d120938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro20008 (p : Pattern) (ha : d1804 p = 1) (hb : d116753 p = 1) : d120940 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d116753 q = 1) : d120860 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19976 q ha hb
    | true =>
      simp only [d1614, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d116753 q = 1) : d120861 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d116753 q = 1) : d120866 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d120866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d120866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d116753 q = 1) : d120867 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d120867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1621, d120867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1645 q = 1) (hb : d116753 q = 1) : d120891 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1645, d120891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1645, d120891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1804 q = 1) (hb : d116753 q = 1) : d120940 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1804, d120940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1804, d120940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20009 (p : Pattern) (ha : d1810 p = 1) (hb : d116753 p = 1) : d120946 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d116753 q = 1) : d120860 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19976 q ha hb
    | true =>
      simp only [d1614, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d116753 q = 1) : d120861 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d116753 q = 1) : d120866 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d120866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d120866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1654 q = 1) (hb : d116753 q = 1) : d120900 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1654, d120900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1654, d120900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1655 q = 1) (hb : d116753 q = 1) : d120901 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1655, d120901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1655, d120901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1810 q = 1) (hb : d116753 q = 1) : d120946 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1810, d120946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1810, d120946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20010 (p : Pattern) (ha : d8983 p = 1) (hb : d116753 p = 1) : d120939 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d116753 q = 1) : d120856 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d120856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19988 q ha hb
    | true =>
      simp only [d8912, d120856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d116753 q = 1) : d120857 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d120857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d120857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d116753 q = 1) : d120860 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19976 q ha hb
    | true =>
      simp only [d1614, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d116753 q = 1) : d120861 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8914 q = 1) (hb : d116753 q = 1) : d120862 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, d120862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8914, d120862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8915 q = 1) (hb : d116753 q = 1) : d120863 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8915, d120863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8915, d120863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8936 q = 1) (hb : d116753 q = 1) : d120889 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8936, d120889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8936, d120889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8983 q = 1) (hb : d116753 q = 1) : d120939 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8983, d120939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8983, d120939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro20011 (p : Pattern) (ha : d8988 p = 1) (hb : d116753 p = 1) : d120945 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d116753 q = 1) : d120856 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d120856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19988 q ha hb
    | true =>
      simp only [d8912, d120856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d116753 q = 1) : d120857 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d120857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d120857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d116753 q = 1) : d120860 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19976 q ha hb
    | true =>
      simp only [d1614, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d116753 q = 1) : d120861 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8914 q = 1) (hb : d116753 q = 1) : d120862 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, d120862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8914, d120862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8942 q = 1) (hb : d116753 q = 1) : d120897 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8942, d120897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8942, d120897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8943 q = 1) (hb : d116753 q = 1) : d120898 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8943, d120898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8943, d120898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8988 q = 1) (hb : d116753 q = 1) : d120945 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8988, d120945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8988, d120945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro20012 (p : Pattern) (ha : d8992 p = 1) (hb : d116753 p = 1) : d120950 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8951 q = 1) (hb : d116753 q = 1) : d120913 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8951, d120913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20004 q ha hb
    | true =>
      simp only [d8951, d120913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8952 q = 1) (hb : d116753 q = 1) : d120914 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8952, d120914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8952, d120914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7037 q = 1) (hb : d116753 q = 1) : d120917 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7037, d120917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19995 q ha hb
    | true =>
      simp only [d7037, d120917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7038 q = 1) (hb : d116753 q = 1) : d120918 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7038, d120918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7038, d120918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8953 q = 1) (hb : d116753 q = 1) : d120919 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8953, d120919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8953, d120919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8954 q = 1) (hb : d116753 q = 1) : d120920 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8954, d120920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8954, d120920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8955 q = 1) (hb : d116753 q = 1) : d120921 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8955, d120921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8955, d120921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8992 q = 1) (hb : d116753 q = 1) : d120950 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8992, d120950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8992, d120950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro20013 (p : Pattern) (ha : d8993 p = 1) (hb : d116753 p = 1) : d120951 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7037 q = 1) (hb : d116753 q = 1) : d120917 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7037, d120917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19995 q ha hb
    | true =>
      simp only [d7037, d120917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7038 q = 1) (hb : d116753 q = 1) : d120918 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7038, d120918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7038, d120918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d116753 q = 1) : d120860 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19976 q ha hb
    | true =>
      simp only [d1614, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d116753 q = 1) : d120861 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8957 q = 1) (hb : d116753 q = 1) : d120923 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8957, d120923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8957, d120923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8958 q = 1) (hb : d116753 q = 1) : d120924 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8958, d120924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8958, d120924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8959 q = 1) (hb : d116753 q = 1) : d120925 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8959, d120925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8959, d120925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8993 q = 1) (hb : d116753 q = 1) : d120951 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8993, d120951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8993, d120951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro20014 (p : Pattern) (ha : d8998 p = 1) (hb : d116753 p = 1) : d120954 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d116753 q = 1) : d120856 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d120856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19988 q ha hb
    | true =>
      simp only [d8912, d120856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d116753 q = 1) : d120857 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d120857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d120857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8973 q = 1) (hb : d116753 q = 1) : d120929 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8973, d120929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8973, d120929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8974 q = 1) (hb : d116753 q = 1) : d120930 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8974, d120930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8974, d120930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8975 q = 1) (hb : d116753 q = 1) : d120931 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8975, d120931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8975, d120931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8998 q = 1) (hb : d116753 q = 1) : d120954 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8998, d120954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8998, d120954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20015 (p : Pattern) (ha : d94396 p = 1) (hb : d116753 p = 1) : d120960 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8938 q = 1) (hb : d116753 q = 1) : d120893 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8938, d120893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20000 q ha hb
    | true =>
      simp only [d8938, d120893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19998 q ha hb
  have h2 (q : Pattern) (ha : d8939 q = 1) (hb : d116753 q = 1) : d120894 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8939, d120894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8939, d120894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8940 q = 1) (hb : d116753 q = 1) : d120895 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8940, d120895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8940, d120895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8941 q = 1) (hb : d116753 q = 1) : d120896 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8941, d120896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8941, d120896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8945 q = 1) (hb : d116753 q = 1) : d120903 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8945, d120903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20001 q ha hb
    | true =>
      simp only [d8945, d120903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19999 q ha hb
  have h6 (q : Pattern) (ha : d8946 q = 1) (hb : d116753 q = 1) : d120904 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8946, d120904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8946, d120904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8947 q = 1) (hb : d116753 q = 1) : d120905 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8947, d120905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8947, d120905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8961 q = 1) (hb : d116753 q = 1) : d120927 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8961, d120927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20005 q ha hb
    | true =>
      simp only [d8961, d120927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19996 q ha hb
  have h9 (q : Pattern) (ha : d94387 q = 1) (hb : d116753 q = 1) : d120928 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94387, d120928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94387, d120928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8977 q = 1) (hb : d116753 q = 1) : d120933 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8977, d120933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20006 q ha hb
    | true =>
      simp only [d8977, d120933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8978 q = 1) (hb : d116753 q = 1) : d120934 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8978, d120934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8978, d120934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94388 q = 1) (hb : d116753 q = 1) : d120935 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94388, d120935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94388, d120935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94389 q = 1) (hb : d116753 q = 1) : d120936 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94389, d120936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94389, d120936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94390 q = 1) (hb : d116753 q = 1) : d120937 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94390, d120937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94390, d120937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d8984 q = 1) (hb : d116753 q = 1) : d120941 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8984, d120941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20010 q ha hb
    | true =>
      simp only [d8984, d120941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20008 q ha hb
  have h16 (q : Pattern) (ha : d8985 q = 1) (hb : d116753 q = 1) : d120942 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8985, d120942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8985, d120942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d8986 q = 1) (hb : d116753 q = 1) : d120943 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8986, d120943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d8986, d120943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d8987 q = 1) (hb : d116753 q = 1) : d120944 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8987, d120944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8987, d120944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d8989 q = 1) (hb : d116753 q = 1) : d120947 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8989, d120947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20011 q ha hb
    | true =>
      simp only [d8989, d120947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20009 q ha hb
  have h20 (q : Pattern) (ha : d8990 q = 1) (hb : d116753 q = 1) : d120948 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8990, d120948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8990, d120948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d8991 q = 1) (hb : d116753 q = 1) : d120949 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8991, d120949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d8991, d120949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d8994 q = 1) (hb : d116753 q = 1) : d120952 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8994, d120952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20012 q ha hb
    | true =>
      simp only [d8994, d120952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20013 q ha hb
  have h23 (q : Pattern) (ha : d94392 q = 1) (hb : d116753 q = 1) : d120953 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94392, d120953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d94392, d120953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d8999 q = 1) (hb : d116753 q = 1) : d120955 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8999, d120955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20014 q ha hb
    | true =>
      simp only [d8999, d120955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d9000 q = 1) (hb : d116753 q = 1) : d120956 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9000, d120956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d9000, d120956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d94393 q = 1) (hb : d116753 q = 1) : d120957 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94393, d120957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d94393, d120957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d94394 q = 1) (hb : d116753 q = 1) : d120958 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94394, d120958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94394, d120958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d94395 q = 1) (hb : d116753 q = 1) : d120959 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94395, d120959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94395, d120959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d94396 q = 1) (hb : d116753 q = 1) : d120960 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94396, d120960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94396, d120960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro20016 (p : Pattern) (ha : d94403 p = 1) (hb : d116753 p = 1) : d120985 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8994 q = 1) (hb : d116753 q = 1) : d120952 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8994, d120952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20012 q ha hb
    | true =>
      simp only [d8994, d120952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20013 q ha hb
  have h2 (q : Pattern) (ha : d94392 q = 1) (hb : d116753 q = 1) : d120953 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94392, d120953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94392, d120953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8999 q = 1) (hb : d116753 q = 1) : d120955 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8999, d120955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20014 q ha hb
    | true =>
      simp only [d8999, d120955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9000 q = 1) (hb : d116753 q = 1) : d120956 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9000, d120956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9000, d120956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94393 q = 1) (hb : d116753 q = 1) : d120957 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94393, d120957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94393, d120957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94401 q = 1) (hb : d116753 q = 1) : d120983 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94401, d120983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94401, d120983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94402 q = 1) (hb : d116753 q = 1) : d120984 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94402, d120984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94402, d120984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94403 q = 1) (hb : d116753 q = 1) : d120985 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94403, d120985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94403, d120985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20017 (p : Pattern) (ha : d1873 p = 1) (hb : d116752 p = 1) : d120994 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1866 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1862 q = 1) (hb : d116750 q = 1) : d22508 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1862, d22508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1862, d22508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19986 q ha hb
  have h3 (q : Pattern) (ha : d1570 q = 1) (hb : d116750 q = 1) : d22220 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d22220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19986 q ha hb
    | true =>
      simp only [d1570, d22220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1863 q = 1) (hb : d116750 q = 1) : d22509 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1863, d22509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1863, d22509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1571 q = 1) (hb : d116750 q = 1) : d22221 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d22221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1571, d22221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1864 q = 1) (hb : d116750 q = 1) : d22510 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1864, d22510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1864, d22510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1865 q = 1) (hb : d116750 q = 1) : d22511 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1865, d22511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1865, d22511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1868 q = 1) (hb : d116750 q = 1) : d22529 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1868, d22529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1868, d22529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19973 q ha hb
  have h9 (q : Pattern) (ha : d1582 q = 1) (hb : d116750 q = 1) : d22233 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d22233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19973 q ha hb
    | true =>
      simp only [d1582, d22233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d1869 q = 1) (hb : d116750 q = 1) : d22530 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1869, d22530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1869, d22530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1583 q = 1) (hb : d116750 q = 1) : d22234 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d22234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1583, d22234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d1870 q = 1) (hb : d116750 q = 1) : d22531 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1870, d22531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1870, d22531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1871 q = 1) (hb : d116750 q = 1) : d22532 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1871, d22532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1871, d22532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d1872 q = 1) (hb : d116750 q = 1) : d22533 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1872, d22533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1872, d22533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d1873 q = 1) (hb : d116752 q = 1) : d120994 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1873, d116752, d120994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1873, d116752, d120994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro20018 (p : Pattern) (ha : d6495 p = 1) (hb : d116752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1872 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6495 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6495, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6495, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro20019 (p : Pattern) (ha : d6501 p = 1) (hb : d116752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6500 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6501 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6501, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6501, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro20020 (p : Pattern) (ha : d7082 p = 1) (hb : d116753 p = 1) : d121009 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1879 q = 1) (hb : d116752 q = 1) : d121000 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, d121000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20017 q ha hb
    | true =>
      simp only [d1879, d121000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19981 q ha hb
  have h2 (q : Pattern) (ha : d1880 q = 1) (hb : d116752 q = 1) : d121001 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, d121001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1880, d121001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1881 q = 1) (hb : d116752 q = 1) : d121002 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, d121002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1881, d121002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7080 q = 1) (hb : d116753 q = 1) : d121003 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7080, d116753, d121003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7080, d116753, d121003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6502 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20018 q ha hb
    | true =>
      simp only [d6502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20019 q ha hb
  have h7 (q : Pattern) (ha : d6503 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6504 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6505 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6505, d116753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6505, d116753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d7081 q = 1) (hb : d116753 q = 1) : d121008 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7081, d121008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7081, d121008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d7082 q = 1) (hb : d116753 q = 1) : d121009 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7082, d121009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7082, d121009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro20021 (p : Pattern) (ha : d1867 p = 1) (hb : d116752 p = 1) : d120993 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1861 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1857 q = 1) (hb : d116750 q = 1) : d17004 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1857, d17004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1857, d17004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20002 q ha hb
  have h3 (q : Pattern) (ha : d1555 q = 1) (hb : d116750 q = 1) : d10036 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d10036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20002 q ha hb
    | true =>
      simp only [d1555, d10036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1858 q = 1) (hb : d116750 q = 1) : d17005 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1858, d17005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1858, d17005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1556 q = 1) (hb : d116750 q = 1) : d10038 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d10038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1556, d10038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1859 q = 1) (hb : d116750 q = 1) : d17006 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1859, d17006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1859, d17006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1860 q = 1) (hb : d116750 q = 1) : d17007 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1860, d17007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1860, d17007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1862 q = 1) (hb : d116750 q = 1) : d22508 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1862, d22508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1862, d22508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19986 q ha hb
  have h9 (q : Pattern) (ha : d1570 q = 1) (hb : d116750 q = 1) : d22220 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d22220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19986 q ha hb
    | true =>
      simp only [d1570, d22220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d1863 q = 1) (hb : d116750 q = 1) : d22509 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1863, d22509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1863, d22509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1571 q = 1) (hb : d116750 q = 1) : d22221 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d22221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1571, d22221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d1864 q = 1) (hb : d116750 q = 1) : d22510 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1864, d22510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1864, d22510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1865 q = 1) (hb : d116750 q = 1) : d22511 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1865, d22511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1865, d22511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d1866 q = 1) (hb : d116750 q = 1) : d22512 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1866, d22512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1866, d22512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d1867 q = 1) (hb : d116752 q = 1) : d120993 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1867, d116752, d120993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1867, d116752, d120993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro20022 (p : Pattern) (ha : d9026 p = 1) (hb : d116753 p = 1) : d121005 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1874 q = 1) (hb : d116752 q = 1) : d120995 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1874, d120995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20021 q ha hb
    | true =>
      simp only [d1874, d120995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20017 q ha hb
  have h2 (q : Pattern) (ha : d1875 q = 1) (hb : d116752 q = 1) : d120996 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1875, d120996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1875, d120996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1876 q = 1) (hb : d116752 q = 1) : d120997 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1876, d120997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1876, d120997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d9024 q = 1) (hb : d116753 q = 1) : d120998 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9024, d116753, d120998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9024, d116753, d120998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1879 q = 1) (hb : d116752 q = 1) : d121000 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, d121000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20017 q ha hb
    | true =>
      simp only [d1879, d121000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19981 q ha hb
  have h7 (q : Pattern) (ha : d1880 q = 1) (hb : d116752 q = 1) : d121001 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, d121001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1880, d121001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1881 q = 1) (hb : d116752 q = 1) : d121002 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, d121002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1881, d121002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7080 q = 1) (hb : d116753 q = 1) : d121003 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7080, d116753, d121003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7080, d116753, d121003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d9025 q = 1) (hb : d116753 q = 1) : d121004 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9025, d121004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9025, d121004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d9026 q = 1) (hb : d116753 q = 1) : d121005 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9026, d121005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9026, d121005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro20023 (p : Pattern) (ha : d9032 p = 1) (hb : d116753 p = 1) : d121015 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9027 q = 1) (hb : d116753 q = 1) : d121006 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9027, d121006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20022 q ha hb
    | true =>
      simp only [d9027, d121006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9028 q = 1) (hb : d116753 q = 1) : d121007 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9028, d121007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9028, d121007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7083 q = 1) (hb : d116753 q = 1) : d121010 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7083, d121010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20020 q ha hb
    | true =>
      simp only [d7083, d121010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7084 q = 1) (hb : d116753 q = 1) : d121011 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7084, d121011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7084, d121011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9029 q = 1) (hb : d116753 q = 1) : d121012 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9029, d121012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9029, d121012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9030 q = 1) (hb : d116753 q = 1) : d121013 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9030, d121013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9030, d121013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9031 q = 1) (hb : d116753 q = 1) : d121014 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9031, d121014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9031, d121014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9032 q = 1) (hb : d116753 q = 1) : d121015 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9032, d121015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9032, d121015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro20024 (p : Pattern) (ha : d9036 p = 1) (hb : d116753 p = 1) : d121028 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7083 q = 1) (hb : d116753 q = 1) : d121010 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7083, d121010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20020 q ha hb
    | true =>
      simp only [d7083, d121010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7084 q = 1) (hb : d116753 q = 1) : d121011 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7084, d121011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7084, d121011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1908 q = 1) (hb : d116753 q = 1) : d121023 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, d121023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19983 q ha hb
    | true =>
      simp only [d1908, d121023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1909 q = 1) (hb : d116753 q = 1) : d121024 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, d121024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1909, d121024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9033 q = 1) (hb : d116753 q = 1) : d121025 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9033, d121025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9033, d121025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9034 q = 1) (hb : d116753 q = 1) : d121026 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9034, d121026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9034, d121026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9035 q = 1) (hb : d116753 q = 1) : d121027 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9035, d121027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9035, d121027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9036 q = 1) (hb : d116753 q = 1) : d121028 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9036, d121028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9036, d121028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro20025 (p : Pattern) (ha : d9050 p = 1) (hb : d116753 p = 1) : d121032 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1879 q = 1) (hb : d116752 q = 1) : d121000 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, d121000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20017 q ha hb
    | true =>
      simp only [d1879, d121000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19981 q ha hb
  have h2 (q : Pattern) (ha : d1880 q = 1) (hb : d116752 q = 1) : d121001 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, d121001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1880, d121001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1881 q = 1) (hb : d116752 q = 1) : d121002 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, d121002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1881, d121002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7080 q = 1) (hb : d116753 q = 1) : d121003 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7080, d116753, d121003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7080, d116753, d121003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1889 q = 1) (hb : d116752 q = 1) : d121017 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, d121017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19981 q ha hb
    | true =>
      simp only [d1889, d121017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19982 q ha hb
  have h7 (q : Pattern) (ha : d1890 q = 1) (hb : d116752 q = 1) : d121018 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, d121018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1890, d121018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1891 q = 1) (hb : d116752 q = 1) : d121019 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, d121019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1891, d121019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1897 q = 1) (hb : d116753 q = 1) : d121020 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1897, d116753, d121020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1897, d116753, d121020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d9049 q = 1) (hb : d116753 q = 1) : d121031 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9049, d121031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9049, d121031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d9050 q = 1) (hb : d116753 q = 1) : d121032 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9050, d121032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9050, d121032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro20026 (p : Pattern) (ha : d9056 p = 1) (hb : d116753 p = 1) : d121038 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9051 q = 1) (hb : d116753 q = 1) : d121033 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9051, d121033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20025 q ha hb
    | true =>
      simp only [d9051, d121033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9052 q = 1) (hb : d116753 q = 1) : d121034 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9052, d121034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9052, d121034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9053 q = 1) (hb : d116753 q = 1) : d121035 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9053, d121035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9053, d121035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9054 q = 1) (hb : d116753 q = 1) : d121036 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9054, d121036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9054, d121036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9055 q = 1) (hb : d116753 q = 1) : d121037 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9055, d121037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9055, d121037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9056 q = 1) (hb : d116753 q = 1) : d121038 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9056, d121038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9056, d121038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20027 (p : Pattern) (ha : d94413 p = 1) (hb : d116753 p = 1) : d121044 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9037 q = 1) (hb : d116753 q = 1) : d121029 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9037, d121029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20023 q ha hb
    | true =>
      simp only [d9037, d121029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20024 q ha hb
  have h2 (q : Pattern) (ha : d94409 q = 1) (hb : d116753 q = 1) : d121030 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94409, d121030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94409, d121030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9057 q = 1) (hb : d116753 q = 1) : d121039 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9057, d121039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20026 q ha hb
    | true =>
      simp only [d9057, d121039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9058 q = 1) (hb : d116753 q = 1) : d121040 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9058, d121040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9058, d121040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94410 q = 1) (hb : d116753 q = 1) : d121041 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94410, d121041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94410, d121041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94411 q = 1) (hb : d116753 q = 1) : d121042 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94411, d121042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94411, d121042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94412 q = 1) (hb : d116753 q = 1) : d121043 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94412, d121043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94412, d121043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94413 q = 1) (hb : d116753 q = 1) : d121044 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94413, d121044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94413, d121044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20028 (p : Pattern) (ha : d94419 p = 1) (hb : d116753 p = 1) : d121061 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8924 q = 1) (hb : d116753 q = 1) : d120876 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8924, d120876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8924, d120876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19990 q ha hb
  have h2 (q : Pattern) (ha : d8925 q = 1) (hb : d116753 q = 1) : d120877 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8925, d120877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8925, d120877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8933 q = 1) (hb : d116753 q = 1) : d120886 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8933, d120886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19990 q ha hb
    | true =>
      simp only [d8933, d120886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19992 q ha hb
  have h4 (q : Pattern) (ha : d8934 q = 1) (hb : d116753 q = 1) : d120887 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8934, d120887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8934, d120887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8935 q = 1) (hb : d116753 q = 1) : d120888 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8935, d120888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8935, d120888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94397 q = 1) (hb : d116753 q = 1) : d120961 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94397, d120961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20007 q ha hb
    | true =>
      simp only [d94397, d120961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20015 q ha hb
  have h7 (q : Pattern) (ha : d9012 q = 1) (hb : d116753 q = 1) : d120979 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9012, d120979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19997 q ha hb
    | true =>
      simp only [d9012, d120979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19979 q ha hb
  have h8 (q : Pattern) (ha : d94398 q = 1) (hb : d116753 q = 1) : d120980 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94398, d120980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94398, d120980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94399 q = 1) (hb : d116753 q = 1) : d120981 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94399, d120981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94399, d120981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d94400 q = 1) (hb : d116753 q = 1) : d120982 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94400, d120982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94400, d120982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94404 q = 1) (hb : d116753 q = 1) : d120986 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94404, d120986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94404, d120986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20016 q ha hb
  have h12 (q : Pattern) (ha : d1848 q = 1) (hb : d116753 q = 1) : d120988 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1848, d120988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1848, d120988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19980 q ha hb
  have h13 (q : Pattern) (ha : d94405 q = 1) (hb : d116753 q = 1) : d120989 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94405, d120989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94405, d120989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94406 q = 1) (hb : d116753 q = 1) : d120990 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94406, d120990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94406, d120990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94407 q = 1) (hb : d116753 q = 1) : d120991 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94407, d120991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94407, d120991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d94408 q = 1) (hb : d116753 q = 1) : d120992 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94408, d120992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94408, d120992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94414 q = 1) (hb : d116753 q = 1) : d121045 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94414, d121045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94414, d121045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20027 q ha hb
  have h18 (q : Pattern) (ha : d1981 q = 1) (hb : d116753 q = 1) : d121056 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1981, d121056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1981, d121056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19985 q ha hb
  have h19 (q : Pattern) (ha : d94415 q = 1) (hb : d116753 q = 1) : d121057 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94415, d121057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94415, d121057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d94416 q = 1) (hb : d116753 q = 1) : d121058 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94416, d121058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d94416, d121058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d94417 q = 1) (hb : d116753 q = 1) : d121059 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94417, d121059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d94417, d121059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d94418 q = 1) (hb : d116753 q = 1) : d121060 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94418, d121060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94418, d121060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d94419 q = 1) (hb : d116753 q = 1) : d121061 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94419, d121061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94419, d121061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro20029 (p : Pattern) (ha : d94425 p = 1) (hb : d116753 p = 1) : d121067 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94420 q = 1) (hb : d116753 q = 1) : d121062 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94420, d121062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94420, d121062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20028 q ha hb
  have h2 (q : Pattern) (ha : d94421 q = 1) (hb : d116753 q = 1) : d121063 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94421, d121063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94421, d121063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94422 q = 1) (hb : d116753 q = 1) : d121064 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94422, d121064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94422, d121064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94423 q = 1) (hb : d116753 q = 1) : d121065 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94423, d121065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94423, d121065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94424 q = 1) (hb : d116753 q = 1) : d121066 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94424, d121066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94424, d121066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94425 q = 1) (hb : d116753 q = 1) : d121067 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94425, d121067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94425, d121067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20030 (p : Pattern) (ha : d2064 p = 1) (hb : d116750 p = 1) : d22687 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2051 q = 1) : d2051 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2063 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2064 q = 1) (hb : d116750 q = 1) : d22687 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d2064, d116750, d22687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2064, d116750, d22687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro20031 (p : Pattern) (ha : d2072 p = 1) (hb : d116752 p = 1) : d121073 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2069 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2065 q = 1) (hb : d116750 q = 1) : d22688 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d22688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20030 q ha hb
    | true =>
      simp only [d2065, d22688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2066 q = 1) (hb : d116750 q = 1) : d22689 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d22689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2066, d22689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d2067 q = 1) (hb : d116750 q = 1) : d22690 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2067, d22690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2067, d22690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2068 q = 1) (hb : d116750 q = 1) : d22691 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2068, d22691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2068, d22691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d2071 q = 1) (hb : d116750 q = 1) : d22709 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2071, d22709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2071, d22709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d2072 q = 1) (hb : d116752 q = 1) : d121073 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d2072, d116752, d121073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2072, d116752, d121073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20032 (p : Pattern) (ha : d2085 p = 1) (hb : d116752 p = 1) : d121078 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2071 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2084 q = 1) (hb : d116750 q = 1) : d2084 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2085 q = 1) (hb : d116752 q = 1) : d121078 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d2085, d116752, d121078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2085, d116752, d121078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro20033 (p : Pattern) (ha : d2096 p = 1) (hb : d116753 p = 1) : d121088 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2086 q = 1) (hb : d116752 q = 1) : d121079 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2086, d121079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20031 q ha hb
    | true =>
      simp only [d2086, d121079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20032 q ha hb
  have h2 (q : Pattern) (ha : d2087 q = 1) (hb : d116752 q = 1) : d121080 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2087, d121080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2087, d121080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2088 q = 1) (hb : d116752 q = 1) : d121081 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2088, d121081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2088, d121081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2090 q = 1) (hb : d116753 q = 1) : d121082 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2090, d116753, d121082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2090, d116753, d121082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2095 q = 1) (hb : d116753 q = 1) : d121087 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2095, d121087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2095, d121087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2096 q = 1) (hb : d116753 q = 1) : d121088 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2096, d121088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2096, d121088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro20034 (p : Pattern) (ha : d2106 p = 1) (hb : d116753 p = 1) : d121098 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d116753 q = 1) : d121089 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20033 q ha hb
    | true =>
      simp only [d2097, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d116753 q = 1) : d121090 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d116753 q = 1) : d121095 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d121095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d121095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2104 q = 1) (hb : d116753 q = 1) : d121096 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, d121096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2104, d121096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2105 q = 1) (hb : d116753 q = 1) : d121097 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2105, d121097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2105, d121097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2106 q = 1) (hb : d116753 q = 1) : d121098 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2106, d121098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2106, d121098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20035 (p : Pattern) (ha : d2116 p = 1) (hb : d116753 p = 1) : d121108 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d116753 q = 1) : d121089 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20033 q ha hb
    | true =>
      simp only [d2097, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d116753 q = 1) : d121090 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d116753 q = 1) : d121095 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d121095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d121095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2104 q = 1) (hb : d116753 q = 1) : d121096 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, d121096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2104, d121096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2105 q = 1) (hb : d116753 q = 1) : d121097 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2105, d121097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2105, d121097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2116 q = 1) (hb : d116753 q = 1) : d121108 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2116, d121108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2116, d121108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20036 (p : Pattern) (ha : d2316 p = 1) (hb : d116753 p = 1) : d121207 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2305 q = 1) (hb : d116753 q = 1) : d121196 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, d121196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20034 q ha hb
    | true =>
      simp only [d2305, d121196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2306 q = 1) (hb : d116753 q = 1) : d121197 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, d121197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2306, d121197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2307 q = 1) (hb : d116753 q = 1) : d121198 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, d121198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2307, d121198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2308 q = 1) (hb : d116753 q = 1) : d121199 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, d121199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, d121199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2309 q = 1) (hb : d116753 q = 1) : d121200 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, d121200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, d121200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2311 q = 1) (hb : d116753 q = 1) : d121202 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2311, d121202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20035 q ha hb
    | true =>
      simp only [d2311, d121202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2312 q = 1) (hb : d116753 q = 1) : d121203 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2312, d121203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2312, d121203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2313 q = 1) (hb : d116753 q = 1) : d121204 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2313, d121204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2313, d121204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2314 q = 1) (hb : d116753 q = 1) : d121205 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2314, d121205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2314, d121205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2315 q = 1) (hb : d116753 q = 1) : d121206 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2315, d121206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2315, d121206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2316 q = 1) (hb : d116753 q = 1) : d121207 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2316, d121207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2316, d121207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro20037 (p : Pattern) (ha : d2325 p = 1) (hb : d116753 p = 1) : d121216 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2311 q = 1) (hb : d116753 q = 1) : d121202 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2311, d121202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20035 q ha hb
    | true =>
      simp only [d2311, d121202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2312 q = 1) (hb : d116753 q = 1) : d121203 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2312, d121203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2312, d121203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2313 q = 1) (hb : d116753 q = 1) : d121204 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2313, d121204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2313, d121204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2314 q = 1) (hb : d116753 q = 1) : d121205 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2314, d121205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2314, d121205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2315 q = 1) (hb : d116753 q = 1) : d121206 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2315, d121206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2315, d121206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2325 q = 1) (hb : d116753 q = 1) : d121216 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2325, d121216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2325, d121216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20038 (p : Pattern) (ha : d2356 p = 1) (hb : d116752 p = 1) : d121228 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2350 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2346 q = 1) (hb : d116750 q = 1) : d22943 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2346, d22943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2346, d22943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20030 q ha hb
  have h3 (q : Pattern) (ha : d2065 q = 1) (hb : d116750 q = 1) : d22688 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d22688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20030 q ha hb
    | true =>
      simp only [d2065, d22688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d2347 q = 1) (hb : d116750 q = 1) : d22944 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2347, d22944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2347, d22944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2066 q = 1) (hb : d116750 q = 1) : d22689 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d22689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2066, d22689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d2348 q = 1) (hb : d116750 q = 1) : d22945 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2348, d22945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2348, d22945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2349 q = 1) (hb : d116750 q = 1) : d22946 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2349, d22946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2349, d22946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d2355 q = 1) (hb : d116750 q = 1) : d22975 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2355, d22975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2355, d22975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d2356 q = 1) (hb : d116752 q = 1) : d121228 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d2356, d116752, d121228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2356, d116752, d121228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro20039 (p : Pattern) (ha : d2366 p = 1) (hb : d116752 p = 1) : d121245 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2355 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2365 q = 1) (hb : d116750 q = 1) : d2365 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2366 q = 1) (hb : d116752 q = 1) : d121245 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d2366, d116752, d121245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2366, d116752, d121245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro20040 (p : Pattern) (ha : d2385 p = 1) (hb : d116753 p = 1) : d121251 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2367 q = 1) (hb : d116752 q = 1) : d121246 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2367, d121246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20038 q ha hb
    | true =>
      simp only [d2367, d121246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20039 q ha hb
  have h2 (q : Pattern) (ha : d2368 q = 1) (hb : d116752 q = 1) : d121247 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2368, d121247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2368, d121247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2369 q = 1) (hb : d116752 q = 1) : d121248 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2369, d121248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2369, d121248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2375 q = 1) (hb : d116753 q = 1) : d121249 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2375, d116753, d121249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2375, d116753, d121249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2384 q = 1) (hb : d116753 q = 1) : d121250 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2384, d121250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2384, d121250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2385 q = 1) (hb : d116753 q = 1) : d121251 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2385, d121251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2385, d121251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro20041 (p : Pattern) (ha : d2452 p = 1) (hb : d116753 p = 1) : d121278 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2386 q = 1) (hb : d116753 q = 1) : d121252 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2386, d121252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20040 q ha hb
    | true =>
      simp only [d2386, d121252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2387 q = 1) (hb : d116753 q = 1) : d121253 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2387, d121253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2387, d121253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2449 q = 1) (hb : d116753 q = 1) : d121275 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2449, d121275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2449, d121275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2450 q = 1) (hb : d116753 q = 1) : d121276 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2450, d121276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2450, d121276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2451 q = 1) (hb : d116753 q = 1) : d121277 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2451, d121277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2451, d121277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2452 q = 1) (hb : d116753 q = 1) : d121278 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2452, d121278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2452, d121278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20042 (p : Pattern) (ha : d2458 p = 1) (hb : d116753 p = 1) : d121284 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2453 q = 1) (hb : d116753 q = 1) : d121279 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2453, d121279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20041 q ha hb
    | true =>
      simp only [d2453, d121279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2454 q = 1) (hb : d116753 q = 1) : d121280 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2454, d121280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2454, d121280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2455 q = 1) (hb : d116753 q = 1) : d121281 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2455, d121281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2455, d121281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2456 q = 1) (hb : d116753 q = 1) : d121282 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2456, d121282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2456, d121282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2457 q = 1) (hb : d116753 q = 1) : d121283 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2457, d121283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2457, d121283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2458 q = 1) (hb : d116753 q = 1) : d121284 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2458, d121284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2458, d121284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20043 (p : Pattern) (ha : d2052 p = 1) (hb : d116750 p = 1) : d10363 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2033 q = 1) : d2033 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2051 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2052 q = 1) (hb : d116750 q = 1) : d10363 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d2052, d116750, d10363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2052, d116750, d10363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro20044 (p : Pattern) (ha : d2070 p = 1) (hb : d116752 p = 1) : d121072 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2057 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2053 q = 1) (hb : d116750 q = 1) : d10364 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d10364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20043 q ha hb
    | true =>
      simp only [d2053, d10364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2054 q = 1) (hb : d116750 q = 1) : d10366 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d10366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2054, d10366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d2055 q = 1) (hb : d116750 q = 1) : d17153 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2055, d17153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2055, d17153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2056 q = 1) (hb : d116750 q = 1) : d17154 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2056, d17154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2056, d17154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d2065 q = 1) (hb : d116750 q = 1) : d22688 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d22688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20030 q ha hb
    | true =>
      simp only [d2065, d22688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d2066 q = 1) (hb : d116750 q = 1) : d22689 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d22689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2066, d22689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d2067 q = 1) (hb : d116750 q = 1) : d22690 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2067, d22690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2067, d22690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2068 q = 1) (hb : d116750 q = 1) : d22691 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2068, d22691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2068, d22691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d2069 q = 1) (hb : d116750 q = 1) : d22692 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2069, d22692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2069, d22692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2070 q = 1) (hb : d116752 q = 1) : d121072 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d2070, d116752, d121072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2070, d116752, d121072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro20045 (p : Pattern) (ha : d9080 p = 1) (hb : d116753 p = 1) : d121084 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2073 q = 1) (hb : d116752 q = 1) : d121074 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2073, d121074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20044 q ha hb
    | true =>
      simp only [d2073, d121074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20031 q ha hb
  have h2 (q : Pattern) (ha : d2074 q = 1) (hb : d116752 q = 1) : d121075 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2074, d121075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2074, d121075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2075 q = 1) (hb : d116752 q = 1) : d121076 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2075, d121076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2075, d121076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7115 q = 1) (hb : d116753 q = 1) : d121077 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7115, d116753, d121077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7115, d116753, d121077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2086 q = 1) (hb : d116752 q = 1) : d121079 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2086, d121079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20031 q ha hb
    | true =>
      simp only [d2086, d121079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20032 q ha hb
  have h7 (q : Pattern) (ha : d2087 q = 1) (hb : d116752 q = 1) : d121080 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2087, d121080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2087, d121080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2088 q = 1) (hb : d116752 q = 1) : d121081 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2088, d121081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2088, d121081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2090 q = 1) (hb : d116753 q = 1) : d121082 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2090, d116753, d121082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2090, d116753, d121082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d9079 q = 1) (hb : d116753 q = 1) : d121083 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9079, d121083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9079, d121083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d9080 q = 1) (hb : d116753 q = 1) : d121084 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9080, d121084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9080, d121084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro20046 (p : Pattern) (ha : d9086 p = 1) (hb : d116753 p = 1) : d121094 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d116753 q = 1) : d121085 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d121085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20045 q ha hb
    | true =>
      simp only [d9081, d121085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d116753 q = 1) : d121086 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d121086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d121086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d116753 q = 1) : d121089 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20033 q ha hb
    | true =>
      simp only [d2097, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d116753 q = 1) : d121090 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9083 q = 1) (hb : d116753 q = 1) : d121091 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, d121091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9083, d121091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9084 q = 1) (hb : d116753 q = 1) : d121092 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9084, d121092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9084, d121092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9085 q = 1) (hb : d116753 q = 1) : d121093 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9085, d121093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9085, d121093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9086 q = 1) (hb : d116753 q = 1) : d121094 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9086, d121094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9086, d121094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20047 (p : Pattern) (ha : d9092 p = 1) (hb : d116753 p = 1) : d121104 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9087 q = 1) (hb : d116753 q = 1) : d121099 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9087, d121099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20046 q ha hb
    | true =>
      simp only [d9087, d121099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20034 q ha hb
  have h2 (q : Pattern) (ha : d9088 q = 1) (hb : d116753 q = 1) : d121100 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9088, d121100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9088, d121100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9089 q = 1) (hb : d116753 q = 1) : d121101 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9089, d121101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9089, d121101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9090 q = 1) (hb : d116753 q = 1) : d121102 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9090, d121102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9090, d121102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9091 q = 1) (hb : d116753 q = 1) : d121103 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9091, d121103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9091, d121103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9092 q = 1) (hb : d116753 q = 1) : d121104 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9092, d121104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9092, d121104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20048 (p : Pattern) (ha : d9095 p = 1) (hb : d116753 p = 1) : d121107 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d116753 q = 1) : d121085 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d121085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20045 q ha hb
    | true =>
      simp only [d9081, d121085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d116753 q = 1) : d121086 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d121086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d121086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d116753 q = 1) : d121089 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20033 q ha hb
    | true =>
      simp only [d2097, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d116753 q = 1) : d121090 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9083 q = 1) (hb : d116753 q = 1) : d121091 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, d121091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9083, d121091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9084 q = 1) (hb : d116753 q = 1) : d121092 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9084, d121092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9084, d121092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9085 q = 1) (hb : d116753 q = 1) : d121093 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9085, d121093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9085, d121093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9095 q = 1) (hb : d116753 q = 1) : d121107 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9095, d121107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9095, d121107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro20049 (p : Pattern) (ha : d9101 p = 1) (hb : d116753 p = 1) : d121114 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9087 q = 1) (hb : d116753 q = 1) : d121099 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9087, d121099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20046 q ha hb
    | true =>
      simp only [d9087, d121099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20034 q ha hb
  have h2 (q : Pattern) (ha : d9088 q = 1) (hb : d116753 q = 1) : d121100 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9088, d121100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9088, d121100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9089 q = 1) (hb : d116753 q = 1) : d121101 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9089, d121101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9089, d121101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9090 q = 1) (hb : d116753 q = 1) : d121102 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9090, d121102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9090, d121102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9091 q = 1) (hb : d116753 q = 1) : d121103 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9091, d121103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9091, d121103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9096 q = 1) (hb : d116753 q = 1) : d121109 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9096, d121109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20048 q ha hb
    | true =>
      simp only [d9096, d121109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20035 q ha hb
  have h7 (q : Pattern) (ha : d9097 q = 1) (hb : d116753 q = 1) : d121110 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9097, d121110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9097, d121110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9098 q = 1) (hb : d116753 q = 1) : d121111 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9098, d121111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9098, d121111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d9099 q = 1) (hb : d116753 q = 1) : d121112 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9099, d121112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9099, d121112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9100 q = 1) (hb : d116753 q = 1) : d121113 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9100, d121113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9100, d121113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9101 q = 1) (hb : d116753 q = 1) : d121114 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9101, d121114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9101, d121114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro20050 (p : Pattern) (ha : d5237 p = 1) (hb : d116752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2069 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5237 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5237, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5237, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro20051 (p : Pattern) (ha : d5252 p = 1) (hb : d116752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d5251 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5252 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5252, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5252, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro20052 (p : Pattern) (ha : d7117 p = 1) (hb : d116753 p = 1) : d121145 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2073 q = 1) (hb : d116752 q = 1) : d121074 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2073, d121074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20044 q ha hb
    | true =>
      simp only [d2073, d121074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20031 q ha hb
  have h2 (q : Pattern) (ha : d2074 q = 1) (hb : d116752 q = 1) : d121075 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2074, d121075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2074, d121075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2075 q = 1) (hb : d116752 q = 1) : d121076 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2075, d121076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2075, d121076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7115 q = 1) (hb : d116753 q = 1) : d121077 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7115, d116753, d121077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7115, d116753, d121077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5253 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20050 q ha hb
    | true =>
      simp only [d5253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20051 q ha hb
  have h7 (q : Pattern) (ha : d5254 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5255 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5256 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5256, d116753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5256, d116753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d7116 q = 1) (hb : d116753 q = 1) : d121144 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7116, d121144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7116, d121144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d7117 q = 1) (hb : d116753 q = 1) : d121145 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7117, d121145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7117, d121145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro20053 (p : Pattern) (ha : d9129 p = 1) (hb : d116753 p = 1) : d121155 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7118 q = 1) (hb : d116753 q = 1) : d121146 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7118, d121146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20052 q ha hb
    | true =>
      simp only [d7118, d121146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7119 q = 1) (hb : d116753 q = 1) : d121147 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7119, d121147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7119, d121147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d116753 q = 1) : d121089 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20033 q ha hb
    | true =>
      simp only [d2097, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d116753 q = 1) : d121090 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9126 q = 1) (hb : d116753 q = 1) : d121152 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9126, d121152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9126, d121152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9127 q = 1) (hb : d116753 q = 1) : d121153 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9127, d121153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9127, d121153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9128 q = 1) (hb : d116753 q = 1) : d121154 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9128, d121154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9128, d121154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9129 q = 1) (hb : d116753 q = 1) : d121155 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9129, d121155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9129, d121155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20054 (p : Pattern) (ha : d9180 p = 1) (hb : d116753 p = 1) : d121201 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9175 q = 1) (hb : d116753 q = 1) : d121191 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9175, d121191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20053 q ha hb
    | true =>
      simp only [d9175, d121191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20034 q ha hb
  have h2 (q : Pattern) (ha : d9176 q = 1) (hb : d116753 q = 1) : d121192 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9176, d121192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9176, d121192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9177 q = 1) (hb : d116753 q = 1) : d121193 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9177, d121193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9177, d121193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9178 q = 1) (hb : d116753 q = 1) : d121194 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9178, d121194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9178, d121194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9179 q = 1) (hb : d116753 q = 1) : d121195 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9179, d121195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9179, d121195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2305 q = 1) (hb : d116753 q = 1) : d121196 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, d121196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20034 q ha hb
    | true =>
      simp only [d2305, d121196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2306 q = 1) (hb : d116753 q = 1) : d121197 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, d121197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2306, d121197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2307 q = 1) (hb : d116753 q = 1) : d121198 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, d121198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2307, d121198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2308 q = 1) (hb : d116753 q = 1) : d121199 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, d121199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, d121199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2309 q = 1) (hb : d116753 q = 1) : d121200 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, d121200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, d121200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9180 q = 1) (hb : d116753 q = 1) : d121201 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9180, d121201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9180, d121201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro20055 (p : Pattern) (ha : d2129 p = 1) (hb : d116753 p = 1) : d121121 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d116753 q = 1) : d121089 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20033 q ha hb
    | true =>
      simp only [d2097, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d116753 q = 1) : d121090 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d116753 q = 1) : d121095 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d121095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d121095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2104 q = 1) (hb : d116753 q = 1) : d121096 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, d121096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2104, d121096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2128 q = 1) (hb : d116753 q = 1) : d121120 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2128, d121120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2128, d121120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2129 q = 1) (hb : d116753 q = 1) : d121121 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2129, d121121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2129, d121121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20056 (p : Pattern) (ha : d2139 p = 1) (hb : d116753 p = 1) : d121131 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d116753 q = 1) : d121089 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20033 q ha hb
    | true =>
      simp only [d2097, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d116753 q = 1) : d121090 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d116753 q = 1) : d121095 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d121095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d121095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2137 q = 1) (hb : d116753 q = 1) : d121129 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2137, d121129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2137, d121129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2138 q = 1) (hb : d116753 q = 1) : d121130 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2138, d121130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2138, d121130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2139 q = 1) (hb : d116753 q = 1) : d121131 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2139, d121131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2139, d121131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20057 (p : Pattern) (ha : d9106 p = 1) (hb : d116753 p = 1) : d121119 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d116753 q = 1) : d121085 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d121085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20045 q ha hb
    | true =>
      simp only [d9081, d121085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d116753 q = 1) : d121086 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d121086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d121086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d116753 q = 1) : d121089 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20033 q ha hb
    | true =>
      simp only [d2097, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d116753 q = 1) : d121090 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9083 q = 1) (hb : d116753 q = 1) : d121091 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, d121091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9083, d121091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9084 q = 1) (hb : d116753 q = 1) : d121092 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9084, d121092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9084, d121092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9105 q = 1) (hb : d116753 q = 1) : d121118 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9105, d121118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9105, d121118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9106 q = 1) (hb : d116753 q = 1) : d121119 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9106, d121119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9106, d121119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20058 (p : Pattern) (ha : d9113 p = 1) (hb : d116753 p = 1) : d121128 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d116753 q = 1) : d121085 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d121085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20045 q ha hb
    | true =>
      simp only [d9081, d121085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d116753 q = 1) : d121086 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d121086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d121086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d116753 q = 1) : d121089 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20033 q ha hb
    | true =>
      simp only [d2097, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d116753 q = 1) : d121090 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9083 q = 1) (hb : d116753 q = 1) : d121091 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, d121091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9083, d121091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9111 q = 1) (hb : d116753 q = 1) : d121126 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9111, d121126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9111, d121126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9112 q = 1) (hb : d116753 q = 1) : d121127 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9112, d121127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9112, d121127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9113 q = 1) (hb : d116753 q = 1) : d121128 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9113, d121128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9113, d121128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20059 (p : Pattern) (ha : d2034 p = 1) (hb : d116750 p = 1) : d10342 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2012 q = 1) : d2012 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2033 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2034 q = 1) (hb : d116750 q = 1) : d10342 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d2034, d116750, d10342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2034, d116750, d10342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro20060 (p : Pattern) (ha : d2149 p = 1) (hb : d116752 p = 1) : d121135 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2148 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2035 q = 1) (hb : d116750 q = 1) : d10343 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, d10343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20059 q ha hb
    | true =>
      simp only [d2035, d10343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2036 q = 1) (hb : d116750 q = 1) : d10345 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2036, d10345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2036, d10345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d2037 q = 1) (hb : d116750 q = 1) : d17225 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2037, d17225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2037, d17225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2038 q = 1) (hb : d116750 q = 1) : d17226 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2038, d17226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2038, d17226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d2053 q = 1) (hb : d116750 q = 1) : d10364 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d10364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20043 q ha hb
    | true =>
      simp only [d2053, d10364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d2054 q = 1) (hb : d116750 q = 1) : d10366 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d10366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2054, d10366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d2055 q = 1) (hb : d116750 q = 1) : d17153 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2055, d17153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2055, d17153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2056 q = 1) (hb : d116750 q = 1) : d17154 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2056, d17154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2056, d17154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d2057 q = 1) (hb : d116750 q = 1) : d22685 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2057, d22685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2057, d22685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2149 q = 1) (hb : d116752 q = 1) : d121135 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d2149, d116752, d121135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2149, d116752, d121135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro20061 (p : Pattern) (ha : d9119 p = 1) (hb : d116753 p = 1) : d121141 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2150 q = 1) (hb : d116752 q = 1) : d121136 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2150, d121136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20060 q ha hb
    | true =>
      simp only [d2150, d121136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20044 q ha hb
  have h2 (q : Pattern) (ha : d2151 q = 1) (hb : d116752 q = 1) : d121137 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2151, d121137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2151, d121137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2152 q = 1) (hb : d116752 q = 1) : d121138 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2152, d121138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2152, d121138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d9117 q = 1) (hb : d116753 q = 1) : d121139 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9117, d116753, d121139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9117, d116753, d121139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2073 q = 1) (hb : d116752 q = 1) : d121074 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2073, d121074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20044 q ha hb
    | true =>
      simp only [d2073, d121074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20031 q ha hb
  have h7 (q : Pattern) (ha : d2074 q = 1) (hb : d116752 q = 1) : d121075 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2074, d121075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2074, d121075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2075 q = 1) (hb : d116752 q = 1) : d121076 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2075, d121076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2075, d121076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7115 q = 1) (hb : d116753 q = 1) : d121077 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7115, d116753, d121077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7115, d116753, d121077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d9118 q = 1) (hb : d116753 q = 1) : d121140 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9118, d121140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9118, d121140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d9119 q = 1) (hb : d116753 q = 1) : d121141 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9119, d121141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9119, d121141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro20062 (p : Pattern) (ha : d9125 p = 1) (hb : d116753 p = 1) : d121151 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9120 q = 1) (hb : d116753 q = 1) : d121142 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9120, d121142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20061 q ha hb
    | true =>
      simp only [d9120, d121142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9121 q = 1) (hb : d116753 q = 1) : d121143 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9121, d121143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9121, d121143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7118 q = 1) (hb : d116753 q = 1) : d121146 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7118, d121146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20052 q ha hb
    | true =>
      simp only [d7118, d121146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7119 q = 1) (hb : d116753 q = 1) : d121147 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7119, d121147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7119, d121147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9122 q = 1) (hb : d116753 q = 1) : d121148 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9122, d121148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9122, d121148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9123 q = 1) (hb : d116753 q = 1) : d121149 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9123, d121149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9123, d121149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9124 q = 1) (hb : d116753 q = 1) : d121150 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9124, d121150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9124, d121150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9125 q = 1) (hb : d116753 q = 1) : d121151 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9125, d121151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9125, d121151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20063 (p : Pattern) (ha : d9145 p = 1) (hb : d116753 p = 1) : d121161 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d116753 q = 1) : d121085 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d121085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20045 q ha hb
    | true =>
      simp only [d9081, d121085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d116753 q = 1) : d121086 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d121086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d121086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9142 q = 1) (hb : d116753 q = 1) : d121158 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9142, d121158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9142, d121158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9143 q = 1) (hb : d116753 q = 1) : d121159 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9143, d121159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9143, d121159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9144 q = 1) (hb : d116753 q = 1) : d121160 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9144, d121160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9144, d121160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9145 q = 1) (hb : d116753 q = 1) : d121161 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9145, d121161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9145, d121161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20064 (p : Pattern) (ha : d94434 p = 1) (hb : d116753 p = 1) : d121167 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9107 q = 1) (hb : d116753 q = 1) : d121122 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9107, d121122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20057 q ha hb
    | true =>
      simp only [d9107, d121122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20055 q ha hb
  have h2 (q : Pattern) (ha : d9108 q = 1) (hb : d116753 q = 1) : d121123 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9108, d121123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9108, d121123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9109 q = 1) (hb : d116753 q = 1) : d121124 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9109, d121124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9109, d121124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9110 q = 1) (hb : d116753 q = 1) : d121125 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9110, d121125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9110, d121125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9114 q = 1) (hb : d116753 q = 1) : d121132 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9114, d121132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20058 q ha hb
    | true =>
      simp only [d9114, d121132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20056 q ha hb
  have h6 (q : Pattern) (ha : d9115 q = 1) (hb : d116753 q = 1) : d121133 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9115, d121133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9115, d121133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9116 q = 1) (hb : d116753 q = 1) : d121134 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9116, d121134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9116, d121134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9130 q = 1) (hb : d116753 q = 1) : d121156 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9130, d121156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20062 q ha hb
    | true =>
      simp only [d9130, d121156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20053 q ha hb
  have h9 (q : Pattern) (ha : d94430 q = 1) (hb : d116753 q = 1) : d121157 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94430, d121157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94430, d121157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d9146 q = 1) (hb : d116753 q = 1) : d121162 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9146, d121162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20063 q ha hb
    | true =>
      simp only [d9146, d121162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9147 q = 1) (hb : d116753 q = 1) : d121163 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9147, d121163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9147, d121163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94431 q = 1) (hb : d116753 q = 1) : d121164 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94431, d121164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94431, d121164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94432 q = 1) (hb : d116753 q = 1) : d121165 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94432, d121165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94432, d121165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94433 q = 1) (hb : d116753 q = 1) : d121166 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94433, d121166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94433, d121166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94434 q = 1) (hb : d116753 q = 1) : d121167 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94434, d121167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94434, d121167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro20065 (p : Pattern) (ha : d2282 p = 1) (hb : d116753 p = 1) : d121169 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d116753 q = 1) : d121089 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20033 q ha hb
    | true =>
      simp only [d2097, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d116753 q = 1) : d121090 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d116753 q = 1) : d121095 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d121095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d121095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2104 q = 1) (hb : d116753 q = 1) : d121096 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, d121096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2104, d121096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2128 q = 1) (hb : d116753 q = 1) : d121120 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2128, d121120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2128, d121120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2282 q = 1) (hb : d116753 q = 1) : d121169 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2282, d121169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2282, d121169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20066 (p : Pattern) (ha : d2288 p = 1) (hb : d116753 p = 1) : d121175 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d116753 q = 1) : d121089 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20033 q ha hb
    | true =>
      simp only [d2097, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d116753 q = 1) : d121090 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d116753 q = 1) : d121095 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d121095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d121095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2137 q = 1) (hb : d116753 q = 1) : d121129 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2137, d121129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2137, d121129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2138 q = 1) (hb : d116753 q = 1) : d121130 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2138, d121130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2138, d121130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2288 q = 1) (hb : d116753 q = 1) : d121175 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2288, d121175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2288, d121175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20067 (p : Pattern) (ha : d9152 p = 1) (hb : d116753 p = 1) : d121168 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d116753 q = 1) : d121085 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d121085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20045 q ha hb
    | true =>
      simp only [d9081, d121085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d116753 q = 1) : d121086 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d121086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d121086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d116753 q = 1) : d121089 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20033 q ha hb
    | true =>
      simp only [d2097, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d116753 q = 1) : d121090 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9083 q = 1) (hb : d116753 q = 1) : d121091 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, d121091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9083, d121091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9084 q = 1) (hb : d116753 q = 1) : d121092 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9084, d121092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9084, d121092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9105 q = 1) (hb : d116753 q = 1) : d121118 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9105, d121118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9105, d121118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9152 q = 1) (hb : d116753 q = 1) : d121168 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9152, d121168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9152, d121168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro20068 (p : Pattern) (ha : d9157 p = 1) (hb : d116753 p = 1) : d121174 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d116753 q = 1) : d121085 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d121085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20045 q ha hb
    | true =>
      simp only [d9081, d121085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d116753 q = 1) : d121086 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d121086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d121086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d116753 q = 1) : d121089 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20033 q ha hb
    | true =>
      simp only [d2097, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d116753 q = 1) : d121090 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9083 q = 1) (hb : d116753 q = 1) : d121091 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, d121091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9083, d121091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9111 q = 1) (hb : d116753 q = 1) : d121126 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9111, d121126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9111, d121126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9112 q = 1) (hb : d116753 q = 1) : d121127 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9112, d121127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9112, d121127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9157 q = 1) (hb : d116753 q = 1) : d121174 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9157, d121174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9157, d121174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro20069 (p : Pattern) (ha : d9161 p = 1) (hb : d116753 p = 1) : d121179 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9120 q = 1) (hb : d116753 q = 1) : d121142 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9120, d121142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20061 q ha hb
    | true =>
      simp only [d9120, d121142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9121 q = 1) (hb : d116753 q = 1) : d121143 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9121, d121143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9121, d121143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7118 q = 1) (hb : d116753 q = 1) : d121146 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7118, d121146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20052 q ha hb
    | true =>
      simp only [d7118, d121146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7119 q = 1) (hb : d116753 q = 1) : d121147 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7119, d121147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7119, d121147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9122 q = 1) (hb : d116753 q = 1) : d121148 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9122, d121148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9122, d121148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9123 q = 1) (hb : d116753 q = 1) : d121149 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9123, d121149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9123, d121149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9124 q = 1) (hb : d116753 q = 1) : d121150 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9124, d121150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9124, d121150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9161 q = 1) (hb : d116753 q = 1) : d121179 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9161, d121179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9161, d121179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro20070 (p : Pattern) (ha : d9162 p = 1) (hb : d116753 p = 1) : d121180 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7118 q = 1) (hb : d116753 q = 1) : d121146 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7118, d121146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20052 q ha hb
    | true =>
      simp only [d7118, d121146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7119 q = 1) (hb : d116753 q = 1) : d121147 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7119, d121147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7119, d121147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d116753 q = 1) : d121089 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20033 q ha hb
    | true =>
      simp only [d2097, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d116753 q = 1) : d121090 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9126 q = 1) (hb : d116753 q = 1) : d121152 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9126, d121152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9126, d121152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9127 q = 1) (hb : d116753 q = 1) : d121153 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9127, d121153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9127, d121153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9128 q = 1) (hb : d116753 q = 1) : d121154 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9128, d121154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9128, d121154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9162 q = 1) (hb : d116753 q = 1) : d121180 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9162, d121180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9162, d121180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro20071 (p : Pattern) (ha : d9167 p = 1) (hb : d116753 p = 1) : d121183 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d116753 q = 1) : d121085 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d121085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20045 q ha hb
    | true =>
      simp only [d9081, d121085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d116753 q = 1) : d121086 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d121086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d121086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9142 q = 1) (hb : d116753 q = 1) : d121158 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9142, d121158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9142, d121158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9143 q = 1) (hb : d116753 q = 1) : d121159 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9143, d121159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9143, d121159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9144 q = 1) (hb : d116753 q = 1) : d121160 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9144, d121160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9144, d121160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9167 q = 1) (hb : d116753 q = 1) : d121183 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9167, d121183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9167, d121183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20072 (p : Pattern) (ha : d94439 p = 1) (hb : d116753 p = 1) : d121189 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9107 q = 1) (hb : d116753 q = 1) : d121122 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9107, d121122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20057 q ha hb
    | true =>
      simp only [d9107, d121122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20055 q ha hb
  have h2 (q : Pattern) (ha : d9108 q = 1) (hb : d116753 q = 1) : d121123 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9108, d121123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9108, d121123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9109 q = 1) (hb : d116753 q = 1) : d121124 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9109, d121124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9109, d121124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9110 q = 1) (hb : d116753 q = 1) : d121125 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9110, d121125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9110, d121125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9114 q = 1) (hb : d116753 q = 1) : d121132 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9114, d121132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20058 q ha hb
    | true =>
      simp only [d9114, d121132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20056 q ha hb
  have h6 (q : Pattern) (ha : d9115 q = 1) (hb : d116753 q = 1) : d121133 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9115, d121133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9115, d121133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9116 q = 1) (hb : d116753 q = 1) : d121134 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9116, d121134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9116, d121134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9130 q = 1) (hb : d116753 q = 1) : d121156 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9130, d121156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20062 q ha hb
    | true =>
      simp only [d9130, d121156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20053 q ha hb
  have h9 (q : Pattern) (ha : d94430 q = 1) (hb : d116753 q = 1) : d121157 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94430, d121157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94430, d121157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d9146 q = 1) (hb : d116753 q = 1) : d121162 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9146, d121162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20063 q ha hb
    | true =>
      simp only [d9146, d121162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9147 q = 1) (hb : d116753 q = 1) : d121163 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9147, d121163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9147, d121163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94431 q = 1) (hb : d116753 q = 1) : d121164 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94431, d121164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94431, d121164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94432 q = 1) (hb : d116753 q = 1) : d121165 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94432, d121165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94432, d121165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94433 q = 1) (hb : d116753 q = 1) : d121166 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94433, d121166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94433, d121166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d9153 q = 1) (hb : d116753 q = 1) : d121170 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9153, d121170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20067 q ha hb
    | true =>
      simp only [d9153, d121170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20065 q ha hb
  have h16 (q : Pattern) (ha : d9154 q = 1) (hb : d116753 q = 1) : d121171 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9154, d121171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9154, d121171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9155 q = 1) (hb : d116753 q = 1) : d121172 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9155, d121172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9155, d121172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d9156 q = 1) (hb : d116753 q = 1) : d121173 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9156, d121173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9156, d121173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d9158 q = 1) (hb : d116753 q = 1) : d121176 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9158, d121176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20068 q ha hb
    | true =>
      simp only [d9158, d121176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20066 q ha hb
  have h20 (q : Pattern) (ha : d9159 q = 1) (hb : d116753 q = 1) : d121177 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9159, d121177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9159, d121177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d9160 q = 1) (hb : d116753 q = 1) : d121178 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9160, d121178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d9160, d121178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d9163 q = 1) (hb : d116753 q = 1) : d121181 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9163, d121181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20069 q ha hb
    | true =>
      simp only [d9163, d121181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20070 q ha hb
  have h23 (q : Pattern) (ha : d94435 q = 1) (hb : d116753 q = 1) : d121182 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94435, d121182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d94435, d121182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d9168 q = 1) (hb : d116753 q = 1) : d121184 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9168, d121184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20071 q ha hb
    | true =>
      simp only [d9168, d121184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d9169 q = 1) (hb : d116753 q = 1) : d121185 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9169, d121185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d9169, d121185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d94436 q = 1) (hb : d116753 q = 1) : d121186 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94436, d121186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d94436, d121186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d94437 q = 1) (hb : d116753 q = 1) : d121187 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94437, d121187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94437, d121187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d94438 q = 1) (hb : d116753 q = 1) : d121188 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94438, d121188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94438, d121188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d94439 q = 1) (hb : d116753 q = 1) : d121189 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94439, d121189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94439, d121189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro20073 (p : Pattern) (ha : d94446 p = 1) (hb : d116753 p = 1) : d121214 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9163 q = 1) (hb : d116753 q = 1) : d121181 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9163, d121181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20069 q ha hb
    | true =>
      simp only [d9163, d121181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20070 q ha hb
  have h2 (q : Pattern) (ha : d94435 q = 1) (hb : d116753 q = 1) : d121182 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94435, d121182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94435, d121182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9168 q = 1) (hb : d116753 q = 1) : d121184 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9168, d121184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20071 q ha hb
    | true =>
      simp only [d9168, d121184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9169 q = 1) (hb : d116753 q = 1) : d121185 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9169, d121185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9169, d121185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94436 q = 1) (hb : d116753 q = 1) : d121186 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94436, d121186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94436, d121186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94444 q = 1) (hb : d116753 q = 1) : d121212 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94444, d121212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94444, d121212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94445 q = 1) (hb : d116753 q = 1) : d121213 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94445, d121213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94445, d121213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94446 q = 1) (hb : d116753 q = 1) : d121214 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94446, d121214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94446, d121214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20074 (p : Pattern) (ha : d2351 p = 1) (hb : d116752 p = 1) : d121223 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2344 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2340 q = 1) (hb : d116750 q = 1) : d17376 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2340, d17376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2340, d17376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20043 q ha hb
  have h3 (q : Pattern) (ha : d2053 q = 1) (hb : d116750 q = 1) : d10364 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d10364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20043 q ha hb
    | true =>
      simp only [d2053, d10364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d2341 q = 1) (hb : d116750 q = 1) : d17377 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2341, d17377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2341, d17377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2054 q = 1) (hb : d116750 q = 1) : d10366 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d10366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2054, d10366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d2342 q = 1) (hb : d116750 q = 1) : d17378 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2342, d17378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2342, d17378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2343 q = 1) (hb : d116750 q = 1) : d17379 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2343, d17379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2343, d17379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d2346 q = 1) (hb : d116750 q = 1) : d22943 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2346, d22943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2346, d22943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20030 q ha hb
  have h9 (q : Pattern) (ha : d2065 q = 1) (hb : d116750 q = 1) : d22688 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d22688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20030 q ha hb
    | true =>
      simp only [d2065, d22688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d2347 q = 1) (hb : d116750 q = 1) : d22944 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2347, d22944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2347, d22944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2066 q = 1) (hb : d116750 q = 1) : d22689 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d22689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2066, d22689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d2348 q = 1) (hb : d116750 q = 1) : d22945 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2348, d22945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2348, d22945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d2349 q = 1) (hb : d116750 q = 1) : d22946 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2349, d22946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2349, d22946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d2350 q = 1) (hb : d116750 q = 1) : d22947 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2350, d22947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2350, d22947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d2351 q = 1) (hb : d116752 q = 1) : d121223 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d2351, d116752, d121223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2351, d116752, d121223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro20075 (p : Pattern) (ha : d6642 p = 1) (hb : d116752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2350 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6642 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6642, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6642, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro20076 (p : Pattern) (ha : d6648 p = 1) (hb : d116752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6647 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6648 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6648, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6648, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro20077 (p : Pattern) (ha : d7163 p = 1) (hb : d116753 p = 1) : d121238 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2357 q = 1) (hb : d116752 q = 1) : d121229 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2357, d121229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20074 q ha hb
    | true =>
      simp only [d2357, d121229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20038 q ha hb
  have h2 (q : Pattern) (ha : d2358 q = 1) (hb : d116752 q = 1) : d121230 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2358, d121230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2358, d121230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2359 q = 1) (hb : d116752 q = 1) : d121231 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2359, d121231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2359, d121231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7161 q = 1) (hb : d116753 q = 1) : d121232 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7161, d116753, d121232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7161, d116753, d121232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6649 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20075 q ha hb
    | true =>
      simp only [d6649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20076 q ha hb
  have h7 (q : Pattern) (ha : d6650 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6651 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6652 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6652, d116753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6652, d116753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d7162 q = 1) (hb : d116753 q = 1) : d121237 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7162, d121237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7162, d121237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d7163 q = 1) (hb : d116753 q = 1) : d121238 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7163, d121238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7163, d121238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro20078 (p : Pattern) (ha : d2345 p = 1) (hb : d116752 p = 1) : d121222 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2339 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2335 q = 1) (hb : d116750 q = 1) : d17369 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2335, d17369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2335, d17369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20059 q ha hb
  have h3 (q : Pattern) (ha : d2035 q = 1) (hb : d116750 q = 1) : d10343 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, d10343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20059 q ha hb
    | true =>
      simp only [d2035, d10343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d2336 q = 1) (hb : d116750 q = 1) : d17370 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2336, d17370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2336, d17370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2036 q = 1) (hb : d116750 q = 1) : d10345 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2036, d10345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2036, d10345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d2337 q = 1) (hb : d116750 q = 1) : d17371 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2337, d17371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2337, d17371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2338 q = 1) (hb : d116750 q = 1) : d17372 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2338, d17372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2338, d17372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d2340 q = 1) (hb : d116750 q = 1) : d17376 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2340, d17376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2340, d17376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20043 q ha hb
  have h9 (q : Pattern) (ha : d2053 q = 1) (hb : d116750 q = 1) : d10364 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d10364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20043 q ha hb
    | true =>
      simp only [d2053, d10364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d2341 q = 1) (hb : d116750 q = 1) : d17377 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2341, d17377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2341, d17377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2054 q = 1) (hb : d116750 q = 1) : d10366 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d10366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2054, d10366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d2342 q = 1) (hb : d116750 q = 1) : d17378 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2342, d17378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2342, d17378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d2343 q = 1) (hb : d116750 q = 1) : d17379 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2343, d17379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2343, d17379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d2344 q = 1) (hb : d116750 q = 1) : d22932 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2344, d22932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2344, d22932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d2345 q = 1) (hb : d116752 q = 1) : d121222 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d2345, d116752, d121222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2345, d116752, d121222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro20079 (p : Pattern) (ha : d9195 p = 1) (hb : d116753 p = 1) : d121234 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2352 q = 1) (hb : d116752 q = 1) : d121224 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2352, d121224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20078 q ha hb
    | true =>
      simp only [d2352, d121224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20074 q ha hb
  have h2 (q : Pattern) (ha : d2353 q = 1) (hb : d116752 q = 1) : d121225 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2353, d121225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2353, d121225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2354 q = 1) (hb : d116752 q = 1) : d121226 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2354, d121226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2354, d121226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d9193 q = 1) (hb : d116753 q = 1) : d121227 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9193, d116753, d121227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9193, d116753, d121227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2357 q = 1) (hb : d116752 q = 1) : d121229 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2357, d121229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20074 q ha hb
    | true =>
      simp only [d2357, d121229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20038 q ha hb
  have h7 (q : Pattern) (ha : d2358 q = 1) (hb : d116752 q = 1) : d121230 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2358, d121230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2358, d121230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2359 q = 1) (hb : d116752 q = 1) : d121231 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2359, d121231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2359, d121231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7161 q = 1) (hb : d116753 q = 1) : d121232 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7161, d116753, d121232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7161, d116753, d121232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d9194 q = 1) (hb : d116753 q = 1) : d121233 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9194, d121233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9194, d121233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d9195 q = 1) (hb : d116753 q = 1) : d121234 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9195, d121234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9195, d121234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro20080 (p : Pattern) (ha : d9201 p = 1) (hb : d116753 p = 1) : d121244 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9196 q = 1) (hb : d116753 q = 1) : d121235 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9196, d121235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20079 q ha hb
    | true =>
      simp only [d9196, d121235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9197 q = 1) (hb : d116753 q = 1) : d121236 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9197, d121236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9197, d121236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7164 q = 1) (hb : d116753 q = 1) : d121239 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7164, d121239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20077 q ha hb
    | true =>
      simp only [d7164, d121239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7165 q = 1) (hb : d116753 q = 1) : d121240 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7165, d121240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7165, d121240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9198 q = 1) (hb : d116753 q = 1) : d121241 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9198, d121241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9198, d121241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9199 q = 1) (hb : d116753 q = 1) : d121242 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9199, d121242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9199, d121242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9200 q = 1) (hb : d116753 q = 1) : d121243 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9200, d121243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9200, d121243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9201 q = 1) (hb : d116753 q = 1) : d121244 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9201, d121244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9201, d121244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro20081 (p : Pattern) (ha : d9205 p = 1) (hb : d116753 p = 1) : d121257 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7164 q = 1) (hb : d116753 q = 1) : d121239 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7164, d121239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20077 q ha hb
    | true =>
      simp only [d7164, d121239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7165 q = 1) (hb : d116753 q = 1) : d121240 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7165, d121240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7165, d121240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2386 q = 1) (hb : d116753 q = 1) : d121252 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2386, d121252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20040 q ha hb
    | true =>
      simp only [d2386, d121252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2387 q = 1) (hb : d116753 q = 1) : d121253 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2387, d121253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2387, d121253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9202 q = 1) (hb : d116753 q = 1) : d121254 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9202, d121254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9202, d121254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9203 q = 1) (hb : d116753 q = 1) : d121255 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9203, d121255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9203, d121255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9204 q = 1) (hb : d116753 q = 1) : d121256 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9204, d121256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9204, d121256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9205 q = 1) (hb : d116753 q = 1) : d121257 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9205, d121257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9205, d121257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro20082 (p : Pattern) (ha : d9219 p = 1) (hb : d116753 p = 1) : d121261 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2357 q = 1) (hb : d116752 q = 1) : d121229 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2357, d121229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20074 q ha hb
    | true =>
      simp only [d2357, d121229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20038 q ha hb
  have h2 (q : Pattern) (ha : d2358 q = 1) (hb : d116752 q = 1) : d121230 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2358, d121230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2358, d121230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2359 q = 1) (hb : d116752 q = 1) : d121231 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2359, d121231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2359, d121231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7161 q = 1) (hb : d116753 q = 1) : d121232 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7161, d116753, d121232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7161, d116753, d121232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2367 q = 1) (hb : d116752 q = 1) : d121246 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2367, d121246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20038 q ha hb
    | true =>
      simp only [d2367, d121246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20039 q ha hb
  have h7 (q : Pattern) (ha : d2368 q = 1) (hb : d116752 q = 1) : d121247 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2368, d121247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2368, d121247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2369 q = 1) (hb : d116752 q = 1) : d121248 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2369, d121248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2369, d121248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2375 q = 1) (hb : d116753 q = 1) : d121249 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2375, d116753, d121249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2375, d116753, d121249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d9218 q = 1) (hb : d116753 q = 1) : d121260 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9218, d121260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9218, d121260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d9219 q = 1) (hb : d116753 q = 1) : d121261 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9219, d121261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9219, d121261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro20083 (p : Pattern) (ha : d9225 p = 1) (hb : d116753 p = 1) : d121267 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9220 q = 1) (hb : d116753 q = 1) : d121262 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9220, d121262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20082 q ha hb
    | true =>
      simp only [d9220, d121262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9221 q = 1) (hb : d116753 q = 1) : d121263 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9221, d121263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9221, d121263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9222 q = 1) (hb : d116753 q = 1) : d121264 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9222, d121264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9222, d121264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9223 q = 1) (hb : d116753 q = 1) : d121265 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9223, d121265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9223, d121265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9224 q = 1) (hb : d116753 q = 1) : d121266 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9224, d121266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9224, d121266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9225 q = 1) (hb : d116753 q = 1) : d121267 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9225, d121267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9225, d121267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20084 (p : Pattern) (ha : d94456 p = 1) (hb : d116753 p = 1) : d121273 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9206 q = 1) (hb : d116753 q = 1) : d121258 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9206, d121258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20080 q ha hb
    | true =>
      simp only [d9206, d121258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20081 q ha hb
  have h2 (q : Pattern) (ha : d94452 q = 1) (hb : d116753 q = 1) : d121259 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94452, d121259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94452, d121259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9226 q = 1) (hb : d116753 q = 1) : d121268 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9226, d121268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20083 q ha hb
    | true =>
      simp only [d9226, d121268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9227 q = 1) (hb : d116753 q = 1) : d121269 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9227, d121269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9227, d121269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94453 q = 1) (hb : d116753 q = 1) : d121270 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94453, d121270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94453, d121270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94454 q = 1) (hb : d116753 q = 1) : d121271 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94454, d121271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94454, d121271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94455 q = 1) (hb : d116753 q = 1) : d121272 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94455, d121272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94455, d121272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94456 q = 1) (hb : d116753 q = 1) : d121273 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94456, d121273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94456, d121273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20085 (p : Pattern) (ha : d94462 p = 1) (hb : d116753 p = 1) : d121290 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9093 q = 1) (hb : d116753 q = 1) : d121105 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9093, d121105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9093, d121105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20047 q ha hb
  have h2 (q : Pattern) (ha : d9094 q = 1) (hb : d116753 q = 1) : d121106 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d9094, d121106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9094, d121106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9102 q = 1) (hb : d116753 q = 1) : d121115 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9102, d121115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20047 q ha hb
    | true =>
      simp only [d9102, d121115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20049 q ha hb
  have h4 (q : Pattern) (ha : d9103 q = 1) (hb : d116753 q = 1) : d121116 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d9103, d121116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9103, d121116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9104 q = 1) (hb : d116753 q = 1) : d121117 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d9104, d121117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9104, d121117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94440 q = 1) (hb : d116753 q = 1) : d121190 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94440, d121190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20064 q ha hb
    | true =>
      simp only [d94440, d121190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20072 q ha hb
  have h7 (q : Pattern) (ha : d9181 q = 1) (hb : d116753 q = 1) : d121208 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9181, d121208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20054 q ha hb
    | true =>
      simp only [d9181, d121208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20036 q ha hb
  have h8 (q : Pattern) (ha : d94441 q = 1) (hb : d116753 q = 1) : d121209 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94441, d121209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94441, d121209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94442 q = 1) (hb : d116753 q = 1) : d121210 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94442, d121210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94442, d121210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d94443 q = 1) (hb : d116753 q = 1) : d121211 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94443, d121211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94443, d121211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94447 q = 1) (hb : d116753 q = 1) : d121215 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94447, d121215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94447, d121215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20073 q ha hb
  have h12 (q : Pattern) (ha : d2326 q = 1) (hb : d116753 q = 1) : d121217 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2326, d121217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2326, d121217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20037 q ha hb
  have h13 (q : Pattern) (ha : d94448 q = 1) (hb : d116753 q = 1) : d121218 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94448, d121218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94448, d121218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94449 q = 1) (hb : d116753 q = 1) : d121219 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94449, d121219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94449, d121219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94450 q = 1) (hb : d116753 q = 1) : d121220 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94450, d121220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94450, d121220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d94451 q = 1) (hb : d116753 q = 1) : d121221 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94451, d121221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94451, d121221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94457 q = 1) (hb : d116753 q = 1) : d121274 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94457, d121274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94457, d121274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20084 q ha hb
  have h18 (q : Pattern) (ha : d2459 q = 1) (hb : d116753 q = 1) : d121285 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2459, d121285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2459, d121285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20042 q ha hb
  have h19 (q : Pattern) (ha : d94458 q = 1) (hb : d116753 q = 1) : d121286 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94458, d121286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94458, d121286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d94459 q = 1) (hb : d116753 q = 1) : d121287 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94459, d121287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d94459, d121287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d94460 q = 1) (hb : d116753 q = 1) : d121288 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94460, d121288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d94460, d121288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d94461 q = 1) (hb : d116753 q = 1) : d121289 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94461, d121289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94461, d121289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d94462 q = 1) (hb : d116753 q = 1) : d121290 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94462, d121290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94462, d121290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro20086 (p : Pattern) (ha : d94468 p = 1) (hb : d116753 p = 1) : d121296 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94463 q = 1) (hb : d116753 q = 1) : d121291 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94463, d121291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94463, d121291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20085 q ha hb
  have h2 (q : Pattern) (ha : d94464 q = 1) (hb : d116753 q = 1) : d121292 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94464, d121292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94464, d121292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94465 q = 1) (hb : d116753 q = 1) : d121293 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94465, d121293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94465, d121293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94466 q = 1) (hb : d116753 q = 1) : d121294 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94466, d121294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94466, d121294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94467 q = 1) (hb : d116753 q = 1) : d121295 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94467, d121295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94467, d121295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94468 q = 1) (hb : d116753 q = 1) : d121296 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94468, d121296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94468, d121296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20087 (p : Pattern) (ha : d94474 p = 1) (hb : d116753 p = 1) : d121302 p = 1 := by
  have h0 (q : Pattern) (ha : d94303 q = 1) (hb : d116753 q = 1) : d120391 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94303, d120391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19817 q ha hb
    | true =>
      simp only [d94303, d120391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19862 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d94343 q = 1) (hb : d116753 q = 1) : d120613 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94343, d120613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94343, d120613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19915 q ha hb
  have h3 (q : Pattern) (ha : d94344 q = 1) (hb : d116753 q = 1) : d120614 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94344, d120614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94344, d120614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94384 q = 1) (hb : d116753 q = 1) : d120840 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94384, d120840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94384, d120840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19972 q ha hb
  have h5 (q : Pattern) (ha : d94385 q = 1) (hb : d116753 q = 1) : d120841 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94385, d120841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94385, d120841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94386 q = 1) (hb : d116753 q = 1) : d120842 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94386, d120842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94386, d120842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94426 q = 1) (hb : d116753 q = 1) : d121068 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94426, d121068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94426, d121068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20029 q ha hb
  have h8 (q : Pattern) (ha : d94427 q = 1) (hb : d116753 q = 1) : d121069 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94427, d121069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94427, d121069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94428 q = 1) (hb : d116753 q = 1) : d121070 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94428, d121070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94428, d121070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94429 q = 1) (hb : d116753 q = 1) : d121071 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d94429, d121071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94429, d121071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94469 q = 1) (hb : d116753 q = 1) : d121297 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94469, d121297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94469, d121297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20086 q ha hb
  have h12 (q : Pattern) (ha : d94470 q = 1) (hb : d116753 q = 1) : d121298 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94470, d121298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94470, d121298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94471 q = 1) (hb : d116753 q = 1) : d121299 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94471, d121299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94471, d121299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94472 q = 1) (hb : d116753 q = 1) : d121300 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d94472, d121300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94472, d121300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94473 q = 1) (hb : d116753 q = 1) : d121301 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d94473, d121301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94473, d121301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d94474 q = 1) (hb : d116753 q = 1) : d121302 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d94474, d121302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94474, d121302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro20088 (p : Pattern) (ha : d94480 p = 1) (hb : d116753 p = 1) : d121308 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94475 q = 1) (hb : d116753 q = 1) : d121303 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d94475, d121303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20087 q ha hb
    | true =>
      simp only [d94475, d121303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94476 q = 1) (hb : d116753 q = 1) : d121304 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d94476, d121304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94476, d121304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94477 q = 1) (hb : d116753 q = 1) : d121305 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d94477, d121305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94477, d121305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94478 q = 1) (hb : d116753 q = 1) : d121306 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d94478, d121306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94478, d121306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94479 q = 1) (hb : d116753 q = 1) : d121307 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d94479, d121307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94479, d121307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94480 q = 1) (hb : d116753 q = 1) : d121308 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d94480, d121308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94480, d121308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20089 (p : Pattern) (ha : d94486 p = 1) (hb : d116753 p = 1) : d121314 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94481 q = 1) (hb : d116753 q = 1) : d121309 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d94481, d121309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20088 q ha hb
    | true =>
      simp only [d94481, d121309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94482 q = 1) (hb : d116753 q = 1) : d121310 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d94482, d121310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94482, d121310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94483 q = 1) (hb : d116753 q = 1) : d121311 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d94483, d121311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94483, d121311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94484 q = 1) (hb : d116753 q = 1) : d121312 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d94484, d121312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94484, d121312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94485 q = 1) (hb : d116753 q = 1) : d121313 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d94485, d121313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94485, d121313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94486 q = 1) (hb : d116753 q = 1) : d121314 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d94486, d121314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94486, d121314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20090 (p : Pattern) (ha : d94492 p = 1) (hb : d116753 p = 1) : d121320 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94487 q = 1) (hb : d116753 q = 1) : d121315 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d94487, d121315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20089 q ha hb
    | true =>
      simp only [d94487, d121315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94488 q = 1) (hb : d116753 q = 1) : d121316 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d94488, d121316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94488, d121316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94489 q = 1) (hb : d116753 q = 1) : d121317 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d94489, d121317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94489, d121317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94490 q = 1) (hb : d116753 q = 1) : d121318 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d94490, d121318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94490, d121318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94491 q = 1) (hb : d116753 q = 1) : d121319 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d94491, d121319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94491, d121319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94492 q = 1) (hb : d116753 q = 1) : d121320 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d94492, d121320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94492, d121320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20091 (p : Pattern) (ha : d94498 p = 1) (hb : d116753 p = 1) : d121326 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94493 q = 1) (hb : d116753 q = 1) : d121321 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d94493, d121321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20090 q ha hb
    | true =>
      simp only [d94493, d121321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94494 q = 1) (hb : d116753 q = 1) : d121322 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d94494, d121322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94494, d121322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94495 q = 1) (hb : d116753 q = 1) : d121323 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d94495, d121323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94495, d121323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94496 q = 1) (hb : d116753 q = 1) : d121324 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d94496, d121324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94496, d121324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94497 q = 1) (hb : d116753 q = 1) : d121325 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d94497, d121325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94497, d121325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94498 q = 1) (hb : d116753 q = 1) : d121326 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d94498, d121326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94498, d121326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20092 (p : Pattern) (ha : d94504 p = 1) (hb : d116753 p = 1) : d121332 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94499 q = 1) (hb : d116753 q = 1) : d121327 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d94499, d121327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20091 q ha hb
    | true =>
      simp only [d94499, d121327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94500 q = 1) (hb : d116753 q = 1) : d121328 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d94500, d121328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94500, d121328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94501 q = 1) (hb : d116753 q = 1) : d121329 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d94501, d121329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94501, d121329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94502 q = 1) (hb : d116753 q = 1) : d121330 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d94502, d121330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94502, d121330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94503 q = 1) (hb : d116753 q = 1) : d121331 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d94503, d121331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94503, d121331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94504 q = 1) (hb : d116753 q = 1) : d121332 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d94504, d121332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94504, d121332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20093 (p : Pattern) (ha : d94510 p = 1) (hb : d116753 p = 1) : d121338 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94505 q = 1) (hb : d116753 q = 1) : d121333 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d94505, d121333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20092 q ha hb
    | true =>
      simp only [d94505, d121333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94506 q = 1) (hb : d116753 q = 1) : d121334 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d94506, d121334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94506, d121334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94507 q = 1) (hb : d116753 q = 1) : d121335 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d94507, d121335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94507, d121335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94508 q = 1) (hb : d116753 q = 1) : d121336 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d94508, d121336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94508, d121336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94509 q = 1) (hb : d116753 q = 1) : d121337 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d94509, d121337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94509, d121337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94510 q = 1) (hb : d116753 q = 1) : d121338 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d94510, d121338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94510, d121338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20094 (p : Pattern) (ha : d94516 p = 1) (hb : d116753 p = 1) : d121344 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94511 q = 1) (hb : d116753 q = 1) : d121339 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d94511, d121339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20093 q ha hb
    | true =>
      simp only [d94511, d121339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94512 q = 1) (hb : d116753 q = 1) : d121340 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d94512, d121340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94512, d121340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94513 q = 1) (hb : d116753 q = 1) : d121341 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d94513, d121341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94513, d121341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94514 q = 1) (hb : d116753 q = 1) : d121342 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d94514, d121342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94514, d121342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94515 q = 1) (hb : d116753 q = 1) : d121343 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d94515, d121343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94515, d121343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94516 q = 1) (hb : d116753 q = 1) : d121344 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d94516, d121344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94516, d121344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20095 (p : Pattern) (ha : d24 p = 1) (hb : d51875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21 q = 1) (hb : d51873 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22 q = 1) (hb : d51874 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d22, d51874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22, d51874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23 q = 1) (hb : d51875 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23, d51875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23, d51875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51875 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d24 q = 1) (hb : d51875 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d24, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20096 (p : Pattern) (ha : d118619 p = 1) (hb : d120066 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d118619 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25 q = 1) (hb : d118615 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d118615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20095 q ha hb
    | true =>
      simp only [d25, d118615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26 q = 1) (hb : d118616 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d118616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26, d118616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d27 q = 1) (hb : d118617 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, d118617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27, d118617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d118618 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, d118618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28, d118618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d29 q = 1) (hb : d118619 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, d118619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29, d118619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d118619 q = 1) (hb : d120066 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d120066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro20097 (p : Pattern) (ha : d118625 p = 1) (hb : d120072 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118620 q = 1) (hb : d120067 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118620, d120067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20096 q ha hb
    | true =>
      simp only [d118620, d120067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118621 q = 1) (hb : d120068 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118621, d120068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118621, d120068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118622 q = 1) (hb : d120069 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118622, d120069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118622, d120069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d118623 q = 1) (hb : d120070 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118623, d120070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118623, d120070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118624 q = 1) (hb : d120071 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d118624, d120071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118624, d120071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d118625 q = 1) (hb : d120072 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d118625, d120072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118625, d120072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20098 (p : Pattern) (ha : d118631 p = 1) (hb : d120078 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118626 q = 1) (hb : d120073 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118626, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20097 q ha hb
    | true =>
      simp only [d118626, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118627 q = 1) (hb : d120074 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118627, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118627, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118628 q = 1) (hb : d120075 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118628, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118628, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118629 q = 1) (hb : d120076 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118629, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118629, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118630 q = 1) (hb : d120077 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118630, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118630, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d118631 q = 1) (hb : d120078 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118631, d120078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118631, d120078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20099 (p : Pattern) (ha : d118637 p = 1) (hb : d120084 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118632 q = 1) (hb : d120079 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118632, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20098 q ha hb
    | true =>
      simp only [d118632, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118633 q = 1) (hb : d120080 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118633, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d118633, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d118634 q = 1) (hb : d120081 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118634, d120081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118634, d120081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118635 q = 1) (hb : d120082 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118635, d120082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118635, d120082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118636 q = 1) (hb : d120083 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118636, d120083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118636, d120083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118637 q = 1) (hb : d120084 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118637, d120084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118637, d120084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20100 (p : Pattern) (ha : d118638 p = 1) (hb : d120085 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118626 q = 1) (hb : d120073 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118626, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20097 q ha hb
    | true =>
      simp only [d118626, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118627 q = 1) (hb : d120074 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118627, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118627, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118628 q = 1) (hb : d120075 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118628, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118628, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118629 q = 1) (hb : d120076 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118629, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118629, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118630 q = 1) (hb : d120077 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118630, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118630, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d118638 q = 1) (hb : d120085 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118638, d120085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118638, d120085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20101 (p : Pattern) (ha : d118644 p = 1) (hb : d120091 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118632 q = 1) (hb : d120079 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118632, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20098 q ha hb
    | true =>
      simp only [d118632, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118633 q = 1) (hb : d120080 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118633, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d118633, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d118634 q = 1) (hb : d120081 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118634, d120081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118634, d120081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118635 q = 1) (hb : d120082 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118635, d120082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118635, d120082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118636 q = 1) (hb : d120083 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118636, d120083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118636, d120083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118639 q = 1) (hb : d120086 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118639, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20100 q ha hb
    | true =>
      simp only [d118639, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d118640 q = 1) (hb : d120087 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118640, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d118640, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d118641 q = 1) (hb : d120088 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118641, d120088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d118641, d120088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d118642 q = 1) (hb : d120089 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118642, d120089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118642, d120089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d118643 q = 1) (hb : d120090 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118643, d120090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118643, d120090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d118644 q = 1) (hb : d120091 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118644, d120091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118644, d120091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro20102 (p : Pattern) (ha : d118649 p = 1) (hb : d120096 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118639 q = 1) (hb : d120086 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118639, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20100 q ha hb
    | true =>
      simp only [d118639, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118640 q = 1) (hb : d120087 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118640, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d118640, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d118641 q = 1) (hb : d120088 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118641, d120088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118641, d120088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118642 q = 1) (hb : d120089 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118642, d120089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118642, d120089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118643 q = 1) (hb : d120090 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118643, d120090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118643, d120090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118649 q = 1) (hb : d120096 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118649, d120096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118649, d120096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20103 (p : Pattern) (ha : d118659 p = 1) (hb : d120102 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d118659 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d66 q = 1) (hb : d118655 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d118655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d66, d118655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20095 q ha hb
  have h3 (q : Pattern) (ha : d25 q = 1) (hb : d118615 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d118615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20095 q ha hb
    | true =>
      simp only [d25, d118615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d67 q = 1) (hb : d118656 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d118656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67, d118656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26 q = 1) (hb : d118616 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d118616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26, d118616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d68 q = 1) (hb : d118657 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d118657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68, d118657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d118658 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d118658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69, d118658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d70 q = 1) (hb : d118659 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, d118659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d70, d118659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d118659 q = 1) (hb : d120102 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d120102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro20104 (p : Pattern) (ha : d118665 p = 1) (hb : d120108 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118660 q = 1) (hb : d120103 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118660, d120103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20103 q ha hb
    | true =>
      simp only [d118660, d120103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118661 q = 1) (hb : d120104 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118661, d120104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118661, d120104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118662 q = 1) (hb : d120105 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118662, d120105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118662, d120105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d118663 q = 1) (hb : d120106 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118663, d120106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118663, d120106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118664 q = 1) (hb : d120107 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d118664, d120107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118664, d120107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d118665 q = 1) (hb : d120108 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d118665, d120108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118665, d120108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20105 (p : Pattern) (ha : d118671 p = 1) (hb : d120114 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118666 q = 1) (hb : d120109 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118666, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20104 q ha hb
    | true =>
      simp only [d118666, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118667 q = 1) (hb : d120110 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118667, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118667, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118668 q = 1) (hb : d120111 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118668, d120111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118668, d120111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118669 q = 1) (hb : d120112 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118669, d120112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118669, d120112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118670 q = 1) (hb : d120113 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118670, d120113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118670, d120113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d118671 q = 1) (hb : d120114 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118671, d120114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118671, d120114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20106 (p : Pattern) (ha : d118677 p = 1) (hb : d120120 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118672 q = 1) (hb : d120115 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118672, d120115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20105 q ha hb
    | true =>
      simp only [d118672, d120115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118673 q = 1) (hb : d120116 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118673, d120116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d118673, d120116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d118674 q = 1) (hb : d120117 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118674, d120117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118674, d120117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118675 q = 1) (hb : d120118 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118675, d120118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118675, d120118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118676 q = 1) (hb : d120119 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118676, d120119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118676, d120119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118677 q = 1) (hb : d120120 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118677, d120120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118677, d120120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20107 (p : Pattern) (ha : d118683 p = 1) (hb : d120126 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118645 q = 1) (hb : d120092 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118645, d120092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20099 q ha hb
    | true =>
      simp only [d118645, d120092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20101 q ha hb
  have h2 (q : Pattern) (ha : d118646 q = 1) (hb : d120093 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118646, d120093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d118646, d120093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d118647 q = 1) (hb : d120094 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d118647, d120094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118647, d120094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118648 q = 1) (hb : d120095 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d118648, d120095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118648, d120095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118650 q = 1) (hb : d120097 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118650, d120097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118650, d120097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20102 q ha hb
  have h6 (q : Pattern) (ha : d118651 q = 1) (hb : d120098 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118651, d120098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118651, d120098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d118652 q = 1) (hb : d120099 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d118652, d120099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d118652, d120099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d118653 q = 1) (hb : d120100 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d118653, d120100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d118653, d120100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d118654 q = 1) (hb : d120101 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d118654, d120101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118654, d120101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d118678 q = 1) (hb : d120121 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118678, d120121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118678, d120121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20106 q ha hb
  have h11 (q : Pattern) (ha : d118679 q = 1) (hb : d120122 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118679, d120122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d118679, d120122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d118680 q = 1) (hb : d120123 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d118680, d120123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d118680, d120123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d118681 q = 1) (hb : d120124 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d118681, d120124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d118681, d120124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d118682 q = 1) (hb : d120125 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d118682, d120125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d118682, d120125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d118683 q = 1) (hb : d120126 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d118683, d120126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d118683, d120126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro20108 (p : Pattern) (ha : d118693 p = 1) (hb : d120136 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118632 q = 1) (hb : d120079 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118632, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20098 q ha hb
    | true =>
      simp only [d118632, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118689 q = 1) (hb : d120132 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118689, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118689, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118690 q = 1) (hb : d120133 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118690, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118690, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118691 q = 1) (hb : d120134 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118691, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118691, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118692 q = 1) (hb : d120135 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118692, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118692, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118693 q = 1) (hb : d120136 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118693, d120136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118693, d120136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20109 (p : Pattern) (ha : d118700 p = 1) (hb : d120143 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118632 q = 1) (hb : d120079 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118632, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20098 q ha hb
    | true =>
      simp only [d118632, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118689 q = 1) (hb : d120132 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118689, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118689, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118690 q = 1) (hb : d120133 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118690, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118690, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118691 q = 1) (hb : d120134 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118691, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118691, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118692 q = 1) (hb : d120135 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118692, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118692, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118639 q = 1) (hb : d120086 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118639, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20100 q ha hb
    | true =>
      simp only [d118639, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d118696 q = 1) (hb : d120139 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118696, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118696, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d118697 q = 1) (hb : d120140 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118697, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d118697, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d118698 q = 1) (hb : d120141 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118698, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118698, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d118699 q = 1) (hb : d120142 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118699, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118699, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d118700 q = 1) (hb : d120143 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118700, d120143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118700, d120143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro20110 (p : Pattern) (ha : d118705 p = 1) (hb : d120148 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118626 q = 1) (hb : d120073 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118626, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20097 q ha hb
    | true =>
      simp only [d118626, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118627 q = 1) (hb : d120074 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118627, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118627, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118628 q = 1) (hb : d120075 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118628, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118628, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118629 q = 1) (hb : d120076 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118629, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118629, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118704 q = 1) (hb : d120147 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118704, d120147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118704, d120147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118705 q = 1) (hb : d120148 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118705, d120148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118705, d120148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20111 (p : Pattern) (ha : d118712 p = 1) (hb : d120155 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118626 q = 1) (hb : d120073 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118626, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20097 q ha hb
    | true =>
      simp only [d118626, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118627 q = 1) (hb : d120074 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118627, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118627, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118628 q = 1) (hb : d120075 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118628, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118628, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118710 q = 1) (hb : d120153 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118710, d120153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118710, d120153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118711 q = 1) (hb : d120154 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118711, d120154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118711, d120154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d118712 q = 1) (hb : d120155 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118712, d120155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118712, d120155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20112 (p : Pattern) (ha : d750 p = 1) (hb : d51988 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d133 q = 1) (hb : d51984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18 q ha hb
    | true =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d134 q = 1) (hb : d51985 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d135 q = 1) (hb : d51986 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d51986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d135, d51986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21 q = 1) (hb : d51873 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d136 q = 1) (hb : d51987 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d136, d51987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d136, d51987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137 q = 1) (hb : d51988 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d137, d51988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137, d51988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51988 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d750 q = 1) (hb : d51988 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro20113 (p : Pattern) (ha : d118720 p = 1) (hb : d120159 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d118720 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d751 q = 1) (hb : d118716 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d118716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20112 q ha hb
    | true =>
      simp only [d751, d118716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d752 q = 1) (hb : d118717 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d118717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d752, d118717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d753 q = 1) (hb : d118718 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d118718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d753, d118718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d754 q = 1) (hb : d118719 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d118719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d754, d118719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d25 q = 1) (hb : d118615 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d118615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20095 q ha hb
    | true =>
      simp only [d25, d118615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d26 q = 1) (hb : d118616 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d118616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26, d118616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d27 q = 1) (hb : d118617 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, d118617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27, d118617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d28 q = 1) (hb : d118618 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, d118618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d28, d118618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d20892 q = 1) (hb : d118720 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d20892, d118720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20892, d118720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d118720 q = 1) (hb : d120159 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d120159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro20114 (p : Pattern) (ha : d118726 p = 1) (hb : d120165 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118721 q = 1) (hb : d120160 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118721, d120160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20113 q ha hb
    | true =>
      simp only [d118721, d120160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20096 q ha hb
  have h2 (q : Pattern) (ha : d118722 q = 1) (hb : d120161 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118722, d120161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118722, d120161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118723 q = 1) (hb : d120162 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118723, d120162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118723, d120162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d118622 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d118724 q = 1) (hb : d120163 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118724, d120163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118724, d120163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d118620 q = 1) (hb : d120067 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118620, d120067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20096 q ha hb
    | true =>
      simp only [d118620, d120067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d118621 q = 1) (hb : d120068 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118621, d120068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118621, d120068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d118622 q = 1) (hb : d120069 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118622, d120069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118622, d120069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d118623 q = 1) (hb : d120070 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118623, d120070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d118623, d120070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d118725 q = 1) (hb : d120164 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d118725, d120164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118725, d120164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d118726 q = 1) (hb : d120165 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d118726, d120165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d118726, d120165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro20115 (p : Pattern) (ha : d118732 p = 1) (hb : d120171 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118727 q = 1) (hb : d120166 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118727, d120166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20114 q ha hb
    | true =>
      simp only [d118727, d120166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118728 q = 1) (hb : d120167 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118728, d120167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118728, d120167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118626 q = 1) (hb : d120073 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118626, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20097 q ha hb
    | true =>
      simp only [d118626, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118627 q = 1) (hb : d120074 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118627, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118627, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118729 q = 1) (hb : d120168 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118729, d120168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118729, d120168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118730 q = 1) (hb : d120169 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118730, d120169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118730, d120169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d118731 q = 1) (hb : d120170 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118731, d120170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d118731, d120170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d118732 q = 1) (hb : d120171 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118732, d120171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118732, d120171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20116 (p : Pattern) (ha : d118738 p = 1) (hb : d120177 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118706 q = 1) (hb : d120149 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118706, d120149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20110 q ha hb
    | true =>
      simp only [d118706, d120149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118707 q = 1) (hb : d120150 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118707, d120150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118707, d120150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118708 q = 1) (hb : d120151 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118708, d120151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118708, d120151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118709 q = 1) (hb : d120152 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118709, d120152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118709, d120152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118713 q = 1) (hb : d120156 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118713, d120156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20111 q ha hb
    | true =>
      simp only [d118713, d120156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d118714 q = 1) (hb : d120157 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118714, d120157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118714, d120157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d118715 q = 1) (hb : d120158 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118715, d120158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d118715, d120158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d118733 q = 1) (hb : d120172 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118733, d120172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20115 q ha hb
    | true =>
      simp only [d118733, d120172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20098 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d118632 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d118734 q = 1) (hb : d120173 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118734, d120173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d118734, d120173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d118632 q = 1) (hb : d120079 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118632, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20098 q ha hb
    | true =>
      simp only [d118632, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d118633 q = 1) (hb : d120080 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118633, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d118633, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d118735 q = 1) (hb : d120174 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118735, d120174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d118735, d120174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d118736 q = 1) (hb : d120175 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118736, d120175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d118736, d120175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d118737 q = 1) (hb : d120176 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118737, d120176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118737, d120176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d118738 q = 1) (hb : d120177 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118738, d120177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118738, d120177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro20117 (p : Pattern) (ha : d118739 p = 1) (hb : d120178 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118626 q = 1) (hb : d120073 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118626, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20097 q ha hb
    | true =>
      simp only [d118626, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118627 q = 1) (hb : d120074 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118627, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118627, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118628 q = 1) (hb : d120075 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118628, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118628, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118629 q = 1) (hb : d120076 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118629, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118629, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118704 q = 1) (hb : d120147 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118704, d120147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118704, d120147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118739 q = 1) (hb : d120178 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118739, d120178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118739, d120178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20118 (p : Pattern) (ha : d118744 p = 1) (hb : d120183 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118626 q = 1) (hb : d120073 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118626, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20097 q ha hb
    | true =>
      simp only [d118626, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118627 q = 1) (hb : d120074 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118627, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118627, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118628 q = 1) (hb : d120075 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118628, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118628, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118710 q = 1) (hb : d120153 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118710, d120153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118710, d120153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118711 q = 1) (hb : d120154 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118711, d120154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118711, d120154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d118744 q = 1) (hb : d120183 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118744, d120183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118744, d120183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20119 (p : Pattern) (ha : d118748 p = 1) (hb : d120187 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118727 q = 1) (hb : d120166 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118727, d120166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20114 q ha hb
    | true =>
      simp only [d118727, d120166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118728 q = 1) (hb : d120167 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118728, d120167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118728, d120167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118626 q = 1) (hb : d120073 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118626, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20097 q ha hb
    | true =>
      simp only [d118626, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118627 q = 1) (hb : d120074 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118627, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118627, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118729 q = 1) (hb : d120168 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118729, d120168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118729, d120168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118730 q = 1) (hb : d120169 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118730, d120169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118730, d120169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d118731 q = 1) (hb : d120170 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118731, d120170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d118731, d120170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d118748 q = 1) (hb : d120187 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118748, d120187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d118748, d120187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20120 (p : Pattern) (ha : d118754 p = 1) (hb : d120193 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118706 q = 1) (hb : d120149 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118706, d120149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20110 q ha hb
    | true =>
      simp only [d118706, d120149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118707 q = 1) (hb : d120150 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118707, d120150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118707, d120150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118708 q = 1) (hb : d120151 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118708, d120151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118708, d120151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118709 q = 1) (hb : d120152 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118709, d120152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118709, d120152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118713 q = 1) (hb : d120156 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118713, d120156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20111 q ha hb
    | true =>
      simp only [d118713, d120156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d118714 q = 1) (hb : d120157 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118714, d120157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118714, d120157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d118715 q = 1) (hb : d120158 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118715, d120158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d118715, d120158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d118733 q = 1) (hb : d120172 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118733, d120172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20115 q ha hb
    | true =>
      simp only [d118733, d120172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20098 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d118632 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d118734 q = 1) (hb : d120173 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118734, d120173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d118734, d120173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d118632 q = 1) (hb : d120079 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118632, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20098 q ha hb
    | true =>
      simp only [d118632, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d118633 q = 1) (hb : d120080 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118633, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d118633, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d118735 q = 1) (hb : d120174 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118735, d120174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d118735, d120174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d118736 q = 1) (hb : d120175 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118736, d120175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d118736, d120175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d118737 q = 1) (hb : d120176 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118737, d120176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118737, d120176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d118740 q = 1) (hb : d120179 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118740, d120179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20117 q ha hb
    | true =>
      simp only [d118740, d120179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d118741 q = 1) (hb : d120180 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118741, d120180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118741, d120180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d118742 q = 1) (hb : d120181 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118742, d120181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d118742, d120181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d118743 q = 1) (hb : d120182 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118743, d120182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118743, d120182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d118745 q = 1) (hb : d120184 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118745, d120184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20118 q ha hb
    | true =>
      simp only [d118745, d120184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d118746 q = 1) (hb : d120185 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118746, d120185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118746, d120185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d118747 q = 1) (hb : d120186 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118747, d120186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d118747, d120186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d118749 q = 1) (hb : d120188 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118749, d120188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20119 q ha hb
    | true =>
      simp only [d118749, d120188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20100 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d118639 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d118750 q = 1) (hb : d120189 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118750, d120189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d118750, d120189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d118639 q = 1) (hb : d120086 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118639, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20100 q ha hb
    | true =>
      simp only [d118639, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d118640 q = 1) (hb : d120087 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118640, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d118640, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d118751 q = 1) (hb : d120190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118751, d120190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d118751, d120190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d118752 q = 1) (hb : d120191 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118752, d120191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d118752, d120191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d118753 q = 1) (hb : d120192 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118753, d120192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d118753, d120192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d118754 q = 1) (hb : d120193 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118754, d120193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d118754, d120193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro20121 (p : Pattern) (ha : d118756 p = 1) (hb : d120195 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118632 q = 1) (hb : d120079 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118632, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20098 q ha hb
    | true =>
      simp only [d118632, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118689 q = 1) (hb : d120132 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118689, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118689, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118690 q = 1) (hb : d120133 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118690, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118690, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118691 q = 1) (hb : d120134 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118691, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118691, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118692 q = 1) (hb : d120135 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118692, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118692, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118756 q = 1) (hb : d120195 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118756, d120195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118756, d120195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20122 (p : Pattern) (ha : d118763 p = 1) (hb : d120202 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118749 q = 1) (hb : d120188 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118749, d120188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20119 q ha hb
    | true =>
      simp only [d118749, d120188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20100 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d118639 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d118750 q = 1) (hb : d120189 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118750, d120189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d118750, d120189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d118639 q = 1) (hb : d120086 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118639, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20100 q ha hb
    | true =>
      simp only [d118639, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118640 q = 1) (hb : d120087 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118640, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118640, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d118751 q = 1) (hb : d120190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118751, d120190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118751, d120190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d118761 q = 1) (hb : d120200 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118761, d120200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118761, d120200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d118762 q = 1) (hb : d120201 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118762, d120201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118762, d120201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d118763 q = 1) (hb : d120202 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118763, d120202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118763, d120202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro20123 (p : Pattern) (ha : d118773 p = 1) (hb : d120208 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d118773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d971 q = 1) (hb : d118769 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d118769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d971, d118769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20112 q ha hb
  have h3 (q : Pattern) (ha : d751 q = 1) (hb : d118716 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d118716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20112 q ha hb
    | true =>
      simp only [d751, d118716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d972 q = 1) (hb : d118770 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d118770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d972, d118770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d752 q = 1) (hb : d118717 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d118717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d752, d118717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d973 q = 1) (hb : d118771 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d118771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d973, d118771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d974 q = 1) (hb : d118772 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d118772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d974, d118772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d66 q = 1) (hb : d118655 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d118655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d66, d118655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20095 q ha hb
  have h9 (q : Pattern) (ha : d25 q = 1) (hb : d118615 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d118615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20095 q ha hb
    | true =>
      simp only [d25, d118615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d67 q = 1) (hb : d118656 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d118656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d67, d118656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26 q = 1) (hb : d118616 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d118616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26, d118616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d68 q = 1) (hb : d118657 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d118657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d68, d118657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d69 q = 1) (hb : d118658 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d118658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69, d118658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d20931 q = 1) (hb : d118773 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d20931, d118773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20931, d118773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d118773 q = 1) (hb : d120208 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d120208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro20124 (p : Pattern) (ha : d118779 p = 1) (hb : d120214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118774 q = 1) (hb : d120209 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118774, d120209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20123 q ha hb
    | true =>
      simp only [d118774, d120209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20103 q ha hb
  have h2 (q : Pattern) (ha : d118775 q = 1) (hb : d120210 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118775, d120210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118775, d120210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118776 q = 1) (hb : d120211 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118776, d120211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118776, d120211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d118662 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d118777 q = 1) (hb : d120212 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118777, d120212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118777, d120212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d118660 q = 1) (hb : d120103 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118660, d120103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20103 q ha hb
    | true =>
      simp only [d118660, d120103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d118661 q = 1) (hb : d120104 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118661, d120104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118661, d120104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d118662 q = 1) (hb : d120105 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118662, d120105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118662, d120105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d118663 q = 1) (hb : d120106 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118663, d120106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d118663, d120106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d118778 q = 1) (hb : d120213 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d118778, d120213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118778, d120213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d118779 q = 1) (hb : d120214 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d118779, d120214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d118779, d120214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro20125 (p : Pattern) (ha : d118785 p = 1) (hb : d120220 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118780 q = 1) (hb : d120215 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118780, d120215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20124 q ha hb
    | true =>
      simp only [d118780, d120215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118781 q = 1) (hb : d120216 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118781, d120216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118781, d120216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118666 q = 1) (hb : d120109 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118666, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20104 q ha hb
    | true =>
      simp only [d118666, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118667 q = 1) (hb : d120110 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118667, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118667, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118782 q = 1) (hb : d120217 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118782, d120217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118782, d120217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118783 q = 1) (hb : d120218 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118783, d120218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118783, d120218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d118784 q = 1) (hb : d120219 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118784, d120219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d118784, d120219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d118785 q = 1) (hb : d120220 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118785, d120220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d118785, d120220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20126 (p : Pattern) (ha : d118791 p = 1) (hb : d120226 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118786 q = 1) (hb : d120221 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118786, d120221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20125 q ha hb
    | true =>
      simp only [d118786, d120221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20105 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d118672 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d118787 q = 1) (hb : d120222 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118787, d120222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d118787, d120222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d118672 q = 1) (hb : d120115 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118672, d120115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20105 q ha hb
    | true =>
      simp only [d118672, d120115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118673 q = 1) (hb : d120116 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118673, d120116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118673, d120116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d118788 q = 1) (hb : d120223 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118788, d120223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118788, d120223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d118789 q = 1) (hb : d120224 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118789, d120224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118789, d120224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d118790 q = 1) (hb : d120225 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118790, d120225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118790, d120225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d118791 q = 1) (hb : d120226 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118791, d120226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118791, d120226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro20127 (p : Pattern) (ha : d118797 p = 1) (hb : d120232 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118694 q = 1) (hb : d120137 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118694, d120137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118694, d120137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20108 q ha hb
  have h2 (q : Pattern) (ha : d118695 q = 1) (hb : d120138 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118695, d120138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d118695, d120138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d118701 q = 1) (hb : d120144 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118701, d120144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20108 q ha hb
    | true =>
      simp only [d118701, d120144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20109 q ha hb
  have h4 (q : Pattern) (ha : d118702 q = 1) (hb : d120145 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118702, d120145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118702, d120145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118703 q = 1) (hb : d120146 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d118703, d120146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118703, d120146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118755 q = 1) (hb : d120194 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118755, d120194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20116 q ha hb
    | true =>
      simp only [d118755, d120194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20120 q ha hb
  have h7 (q : Pattern) (ha : d118757 q = 1) (hb : d120196 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118757, d120196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20121 q ha hb
    | true =>
      simp only [d118757, d120196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d118758 q = 1) (hb : d120197 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118758, d120197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d118758, d120197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d118759 q = 1) (hb : d120198 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d118759, d120198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d118759, d120198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d118760 q = 1) (hb : d120199 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d118760, d120199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118760, d120199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d118764 q = 1) (hb : d120203 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118764, d120203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118764, d120203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20122 q ha hb
  have h12 (q : Pattern) (ha : d118765 q = 1) (hb : d120204 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118765, d120204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d118765, d120204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d118766 q = 1) (hb : d120205 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d118766, d120205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d118766, d120205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d118767 q = 1) (hb : d120206 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d118767, d120206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d118767, d120206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d118768 q = 1) (hb : d120207 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d118768, d120207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d118768, d120207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d118792 q = 1) (hb : d120227 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118792, d120227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118792, d120227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20126 q ha hb
  have h17 (q : Pattern) (ha : d118793 q = 1) (hb : d120228 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118793, d120228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d118793, d120228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d118794 q = 1) (hb : d120229 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d118794, d120229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d118794, d120229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d118795 q = 1) (hb : d120230 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d118795, d120230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d118795, d120230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d118796 q = 1) (hb : d120231 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d118796, d120231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d118796, d120231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d118797 q = 1) (hb : d120232 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d118797, d120232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d118797, d120232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro20128 (p : Pattern) (ha : d118803 p = 1) (hb : d120238 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118684 q = 1) (hb : d120127 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d118684, d120127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118684, d120127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20107 q ha hb
  have h2 (q : Pattern) (ha : d118685 q = 1) (hb : d120128 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d118685, d120128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118685, d120128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118686 q = 1) (hb : d120129 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d118686, d120129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118686, d120129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d118687 q = 1) (hb : d120130 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d118687, d120130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118687, d120130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118688 q = 1) (hb : d120131 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d118688, d120131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118688, d120131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118798 q = 1) (hb : d120233 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d118798, d120233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118798, d120233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20127 q ha hb
  have h7 (q : Pattern) (ha : d118799 q = 1) (hb : d120234 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d118799, d120234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118799, d120234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d118800 q = 1) (hb : d120235 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d118800, d120235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118800, d120235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d118801 q = 1) (hb : d120236 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d118801, d120236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118801, d120236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d118802 q = 1) (hb : d120237 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d118802, d120237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118802, d120237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d118803 q = 1) (hb : d120238 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d118803, d120238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118803, d120238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro20129 (p : Pattern) (ha : d118808 p = 1) (hb : d120243 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118733 q = 1) (hb : d120172 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118733, d120172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20115 q ha hb
    | true =>
      simp only [d118733, d120172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20098 q ha hb
  have h2 (q : Pattern) (ha : d118804 q = 1) (hb : d120239 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118804, d120239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118804, d120239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118805 q = 1) (hb : d120240 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118805, d120240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118805, d120240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118806 q = 1) (hb : d120241 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118806, d120241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118806, d120241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118807 q = 1) (hb : d120242 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118807, d120242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118807, d120242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118808 q = 1) (hb : d120243 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118808, d120243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118808, d120243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20130 (p : Pattern) (ha : d118815 p = 1) (hb : d120250 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118733 q = 1) (hb : d120172 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118733, d120172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20115 q ha hb
    | true =>
      simp only [d118733, d120172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20098 q ha hb
  have h2 (q : Pattern) (ha : d118804 q = 1) (hb : d120239 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118804, d120239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118804, d120239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118805 q = 1) (hb : d120240 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118805, d120240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118805, d120240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118806 q = 1) (hb : d120241 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118806, d120241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118806, d120241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118807 q = 1) (hb : d120242 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118807, d120242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118807, d120242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118749 q = 1) (hb : d120188 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118749, d120188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20119 q ha hb
    | true =>
      simp only [d118749, d120188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20100 q ha hb
  have h7 (q : Pattern) (ha : d118811 q = 1) (hb : d120246 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118811, d120246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118811, d120246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d118812 q = 1) (hb : d120247 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118812, d120247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d118812, d120247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d118813 q = 1) (hb : d120248 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118813, d120248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118813, d120248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d118814 q = 1) (hb : d120249 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118814, d120249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118814, d120249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d118815 q = 1) (hb : d120250 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118815, d120250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118815, d120250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro20131 (p : Pattern) (ha : d118726 p = 1) (hb : d120276 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118721 q = 1) (hb : d120160 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118721, d120160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20113 q ha hb
    | true =>
      simp only [d118721, d120160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20096 q ha hb
  have h2 (q : Pattern) (ha : d118722 q = 1) (hb : d120161 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118722, d120161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118722, d120161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118723 q = 1) (hb : d120162 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118723, d120162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118723, d120162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d118622 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d118724 q = 1) (hb : d120163 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118724, d120163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118724, d120163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d118623 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d118725 q = 1) (hb : d120275 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d118725, d120275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118725, d120275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d118726 q = 1) (hb : d120276 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d118726, d120276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d118726, d120276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20132 (p : Pattern) (ha : d118732 p = 1) (hb : d120286 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118727 q = 1) (hb : d120277 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118727, d120277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20131 q ha hb
    | true =>
      simp only [d118727, d120277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118728 q = 1) (hb : d120278 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118728, d120278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118728, d120278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118626 q = 1) (hb : d120073 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118626, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20097 q ha hb
    | true =>
      simp only [d118626, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118627 q = 1) (hb : d120074 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118627, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118627, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118729 q = 1) (hb : d120283 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118729, d120283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118729, d120283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118730 q = 1) (hb : d120284 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118730, d120284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118730, d120284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d118731 q = 1) (hb : d120285 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118731, d120285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d118731, d120285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d118732 q = 1) (hb : d120286 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118732, d120286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118732, d120286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20133 (p : Pattern) (ha : d118820 p = 1) (hb : d120255 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118727 q = 1) (hb : d120166 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118727, d120166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20114 q ha hb
    | true =>
      simp only [d118727, d120166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118728 q = 1) (hb : d120167 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118728, d120167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118728, d120167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118626 q = 1) (hb : d120073 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118626, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20097 q ha hb
    | true =>
      simp only [d118626, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118627 q = 1) (hb : d120074 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118627, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118627, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118729 q = 1) (hb : d120168 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118729, d120168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118729, d120168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118730 q = 1) (hb : d120169 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118730, d120169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118730, d120169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d118819 q = 1) (hb : d120254 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118819, d120254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118819, d120254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d118820 q = 1) (hb : d120255 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118820, d120255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118820, d120255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20134 (p : Pattern) (ha : d118827 p = 1) (hb : d120262 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118727 q = 1) (hb : d120166 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118727, d120166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20114 q ha hb
    | true =>
      simp only [d118727, d120166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118728 q = 1) (hb : d120167 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118728, d120167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118728, d120167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118626 q = 1) (hb : d120073 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118626, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20097 q ha hb
    | true =>
      simp only [d118626, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118627 q = 1) (hb : d120074 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118627, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118627, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118729 q = 1) (hb : d120168 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118729, d120168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118729, d120168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118825 q = 1) (hb : d120260 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118825, d120260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118825, d120260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d118826 q = 1) (hb : d120261 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118826, d120261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d118826, d120261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d118827 q = 1) (hb : d120262 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118827, d120262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118827, d120262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20135 (p : Pattern) (ha : d20989 p = 1) (hb : d52116 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d313 q = 1) (hb : d52112 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d52112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41 q ha hb
    | true =>
      simp only [d313, d52112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d314 q = 1) (hb : d52113 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d52113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d314, d52113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d133 q = 1) (hb : d51984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18 q ha hb
    | true =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d134 q = 1) (hb : d51985 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d315 q = 1) (hb : d52114 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d52114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315, d52114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d135 q = 1) (hb : d51986 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d51986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d135, d51986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d316 q = 1) (hb : d52115 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d316, d52115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316, d52115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d317 q = 1) (hb : d52116 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d317, d52116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d317, d52116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52116 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d20989 q = 1) (hb : d52116 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d20989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro20136 (p : Pattern) (ha : d118835 p = 1) (hb : d120266 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d118835 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20990 q = 1) (hb : d118831 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d118831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20135 q ha hb
    | true =>
      simp only [d20990, d118831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20991 q = 1) (hb : d118832 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d118832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20991, d118832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d20992 q = 1) (hb : d118833 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d20992, d118833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20992, d118833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20993 q = 1) (hb : d118834 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d20993, d118834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20993, d118834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d751 q = 1) (hb : d118716 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d118716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20112 q ha hb
    | true =>
      simp only [d751, d118716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d752 q = 1) (hb : d118717 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d118717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d752, d118717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d753 q = 1) (hb : d118718 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d118718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d753, d118718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d754 q = 1) (hb : d118719 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d118719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d754, d118719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d20994 q = 1) (hb : d118835 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d20994, d118835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20994, d118835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d118835 q = 1) (hb : d120266 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d120266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro20137 (p : Pattern) (ha : d118841 p = 1) (hb : d120272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118836 q = 1) (hb : d120267 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118836, d120267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20136 q ha hb
    | true =>
      simp only [d118836, d120267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20113 q ha hb
  have h2 (q : Pattern) (ha : d118837 q = 1) (hb : d120268 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118837, d120268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118837, d120268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118838 q = 1) (hb : d120269 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118838, d120269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118838, d120269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d118723 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d118839 q = 1) (hb : d120270 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118839, d120270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118839, d120270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d118721 q = 1) (hb : d120160 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118721, d120160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20113 q ha hb
    | true =>
      simp only [d118721, d120160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20096 q ha hb
  have h7 (q : Pattern) (ha : d118722 q = 1) (hb : d120161 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118722, d120161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118722, d120161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d118723 q = 1) (hb : d120162 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118723, d120162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118723, d120162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d118622 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d118724 q = 1) (hb : d120163 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118724, d120163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d118724, d120163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d118840 q = 1) (hb : d120271 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d118840, d120271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118840, d120271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d118841 q = 1) (hb : d120272 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d118841, d120272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d118841, d120272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro20138 (p : Pattern) (ha : d118847 p = 1) (hb : d120282 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118842 q = 1) (hb : d120273 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118842, d120273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20137 q ha hb
    | true =>
      simp only [d118842, d120273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118843 q = 1) (hb : d120274 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118843, d120274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118843, d120274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118727 q = 1) (hb : d120277 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118727, d120277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20131 q ha hb
    | true =>
      simp only [d118727, d120277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118728 q = 1) (hb : d120278 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118728, d120278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118728, d120278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118844 q = 1) (hb : d120279 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118844, d120279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118844, d120279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118845 q = 1) (hb : d120280 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118845, d120280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118845, d120280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d118846 q = 1) (hb : d120281 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118846, d120281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d118846, d120281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d118847 q = 1) (hb : d120282 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118847, d120282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118847, d120282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20139 (p : Pattern) (ha : d118853 p = 1) (hb : d120292 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118727 q = 1) (hb : d120166 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118727, d120166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20114 q ha hb
    | true =>
      simp only [d118727, d120166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118728 q = 1) (hb : d120167 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118728, d120167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118728, d120167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118850 q = 1) (hb : d120289 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118850, d120289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118850, d120289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118851 q = 1) (hb : d120290 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118851, d120290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118851, d120290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118852 q = 1) (hb : d120291 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118852, d120291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118852, d120291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d118853 q = 1) (hb : d120292 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118853, d120292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118853, d120292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20140 (p : Pattern) (ha : d118859 p = 1) (hb : d120298 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118821 q = 1) (hb : d120256 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118821, d120256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20133 q ha hb
    | true =>
      simp only [d118821, d120256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20110 q ha hb
  have h2 (q : Pattern) (ha : d118822 q = 1) (hb : d120257 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118822, d120257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118822, d120257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118823 q = 1) (hb : d120258 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118823, d120258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118823, d120258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118824 q = 1) (hb : d120259 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118824, d120259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118824, d120259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118828 q = 1) (hb : d120263 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118828, d120263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20134 q ha hb
    | true =>
      simp only [d118828, d120263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20111 q ha hb
  have h6 (q : Pattern) (ha : d118829 q = 1) (hb : d120264 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118829, d120264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118829, d120264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d118830 q = 1) (hb : d120265 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118830, d120265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d118830, d120265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d118848 q = 1) (hb : d120287 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118848, d120287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20138 q ha hb
    | true =>
      simp only [d118848, d120287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20132 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d118733 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d118849 q = 1) (hb : d120288 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118849, d120288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d118849, d120288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d118854 q = 1) (hb : d120293 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118854, d120293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20139 q ha hb
    | true =>
      simp only [d118854, d120293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d118855 q = 1) (hb : d120294 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118855, d120294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d118855, d120294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d118856 q = 1) (hb : d120295 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118856, d120295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d118856, d120295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d118857 q = 1) (hb : d120296 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118857, d120296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d118857, d120296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d118858 q = 1) (hb : d120297 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118858, d120297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118858, d120297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d118859 q = 1) (hb : d120298 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118859, d120298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118859, d120298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro20141 (p : Pattern) (ha : d118748 p = 1) (hb : d120309 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118727 q = 1) (hb : d120277 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118727, d120277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20131 q ha hb
    | true =>
      simp only [d118727, d120277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118728 q = 1) (hb : d120278 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118728, d120278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118728, d120278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118626 q = 1) (hb : d120073 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118626, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20097 q ha hb
    | true =>
      simp only [d118626, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118627 q = 1) (hb : d120074 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118627, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118627, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118729 q = 1) (hb : d120283 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118729, d120283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118729, d120283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118730 q = 1) (hb : d120284 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118730, d120284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118730, d120284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d118731 q = 1) (hb : d120285 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118731, d120285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d118731, d120285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d118748 q = 1) (hb : d120309 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118748, d120309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d118748, d120309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20142 (p : Pattern) (ha : d118860 p = 1) (hb : d120299 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118727 q = 1) (hb : d120166 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118727, d120166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20114 q ha hb
    | true =>
      simp only [d118727, d120166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118728 q = 1) (hb : d120167 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118728, d120167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118728, d120167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118626 q = 1) (hb : d120073 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118626, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20097 q ha hb
    | true =>
      simp only [d118626, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118627 q = 1) (hb : d120074 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118627, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118627, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118729 q = 1) (hb : d120168 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118729, d120168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118729, d120168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118730 q = 1) (hb : d120169 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118730, d120169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118730, d120169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d118819 q = 1) (hb : d120254 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118819, d120254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118819, d120254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d118860 q = 1) (hb : d120299 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118860, d120299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d118860, d120299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20143 (p : Pattern) (ha : d118865 p = 1) (hb : d120304 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118727 q = 1) (hb : d120166 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118727, d120166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20114 q ha hb
    | true =>
      simp only [d118727, d120166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118728 q = 1) (hb : d120167 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118728, d120167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118728, d120167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118626 q = 1) (hb : d120073 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118626, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20097 q ha hb
    | true =>
      simp only [d118626, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118627 q = 1) (hb : d120074 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118627, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118627, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118729 q = 1) (hb : d120168 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118729, d120168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118729, d120168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118825 q = 1) (hb : d120260 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118825, d120260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118825, d120260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d118826 q = 1) (hb : d120261 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118826, d120261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d118826, d120261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d118865 q = 1) (hb : d120304 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118865, d120304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d118865, d120304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20144 (p : Pattern) (ha : d118869 p = 1) (hb : d120308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118842 q = 1) (hb : d120273 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118842, d120273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20137 q ha hb
    | true =>
      simp only [d118842, d120273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118843 q = 1) (hb : d120274 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118843, d120274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118843, d120274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118727 q = 1) (hb : d120277 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118727, d120277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20131 q ha hb
    | true =>
      simp only [d118727, d120277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118728 q = 1) (hb : d120278 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118728, d120278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118728, d120278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118844 q = 1) (hb : d120279 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118844, d120279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118844, d120279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118845 q = 1) (hb : d120280 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118845, d120280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118845, d120280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d118846 q = 1) (hb : d120281 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118846, d120281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d118846, d120281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d118869 q = 1) (hb : d120308 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118869, d120308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d118869, d120308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20145 (p : Pattern) (ha : d118872 p = 1) (hb : d120312 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118727 q = 1) (hb : d120166 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118727, d120166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20114 q ha hb
    | true =>
      simp only [d118727, d120166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118728 q = 1) (hb : d120167 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118728, d120167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118728, d120167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118850 q = 1) (hb : d120289 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118850, d120289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118850, d120289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118851 q = 1) (hb : d120290 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118851, d120290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118851, d120290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118852 q = 1) (hb : d120291 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118852, d120291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118852, d120291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d118872 q = 1) (hb : d120312 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118872, d120312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118872, d120312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20146 (p : Pattern) (ha : d118878 p = 1) (hb : d120318 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118821 q = 1) (hb : d120256 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118821, d120256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20133 q ha hb
    | true =>
      simp only [d118821, d120256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20110 q ha hb
  have h2 (q : Pattern) (ha : d118822 q = 1) (hb : d120257 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118822, d120257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118822, d120257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118823 q = 1) (hb : d120258 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118823, d120258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118823, d120258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118824 q = 1) (hb : d120259 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118824, d120259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118824, d120259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118828 q = 1) (hb : d120263 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118828, d120263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20134 q ha hb
    | true =>
      simp only [d118828, d120263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20111 q ha hb
  have h6 (q : Pattern) (ha : d118829 q = 1) (hb : d120264 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118829, d120264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118829, d120264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d118830 q = 1) (hb : d120265 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118830, d120265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d118830, d120265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d118848 q = 1) (hb : d120287 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118848, d120287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20138 q ha hb
    | true =>
      simp only [d118848, d120287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20132 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d118733 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d118849 q = 1) (hb : d120288 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118849, d120288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d118849, d120288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d118854 q = 1) (hb : d120293 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118854, d120293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20139 q ha hb
    | true =>
      simp only [d118854, d120293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d118855 q = 1) (hb : d120294 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118855, d120294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d118855, d120294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d118856 q = 1) (hb : d120295 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118856, d120295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d118856, d120295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d118857 q = 1) (hb : d120296 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118857, d120296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d118857, d120296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d118858 q = 1) (hb : d120297 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118858, d120297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118858, d120297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d118861 q = 1) (hb : d120300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118861, d120300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20142 q ha hb
    | true =>
      simp only [d118861, d120300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20117 q ha hb
  have h17 (q : Pattern) (ha : d118862 q = 1) (hb : d120301 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118862, d120301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118862, d120301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d118863 q = 1) (hb : d120302 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118863, d120302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d118863, d120302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d118864 q = 1) (hb : d120303 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118864, d120303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118864, d120303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d118866 q = 1) (hb : d120305 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118866, d120305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20143 q ha hb
    | true =>
      simp only [d118866, d120305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20118 q ha hb
  have h21 (q : Pattern) (ha : d118867 q = 1) (hb : d120306 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118867, d120306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118867, d120306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d118868 q = 1) (hb : d120307 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118868, d120307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d118868, d120307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d118870 q = 1) (hb : d120310 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118870, d120310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20144 q ha hb
    | true =>
      simp only [d118870, d120310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20141 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d118749 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d118871 q = 1) (hb : d120311 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118871, d120311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d118871, d120311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d118873 q = 1) (hb : d120313 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118873, d120313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20145 q ha hb
    | true =>
      simp only [d118873, d120313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d118874 q = 1) (hb : d120314 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118874, d120314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d118874, d120314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d118875 q = 1) (hb : d120315 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118875, d120315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d118875, d120315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d118876 q = 1) (hb : d120316 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118876, d120316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d118876, d120316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d118877 q = 1) (hb : d120317 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118877, d120317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d118877, d120317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d118878 q = 1) (hb : d120318 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118878, d120318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d118878, d120318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro20147 (p : Pattern) (ha : d118880 p = 1) (hb : d120325 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118733 q = 1) (hb : d120320 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118733, d120320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20132 q ha hb
    | true =>
      simp only [d118733, d120320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20098 q ha hb
  have h2 (q : Pattern) (ha : d118804 q = 1) (hb : d120321 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118804, d120321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118804, d120321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118805 q = 1) (hb : d120322 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118805, d120322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118805, d120322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118806 q = 1) (hb : d120323 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118806, d120323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118806, d120323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118807 q = 1) (hb : d120324 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118807, d120324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118807, d120324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118632 q = 1) (hb : d120079 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118632, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20098 q ha hb
    | true =>
      simp only [d118632, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d118689 q = 1) (hb : d120132 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118689, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118689, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d118690 q = 1) (hb : d120133 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118690, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d118690, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d118691 q = 1) (hb : d120134 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118691, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118691, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d118692 q = 1) (hb : d120135 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118692, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118692, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d118880 q = 1) (hb : d120325 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118880, d120325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118880, d120325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro20148 (p : Pattern) (ha : d118887 p = 1) (hb : d120332 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118870 q = 1) (hb : d120310 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118870, d120310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20144 q ha hb
    | true =>
      simp only [d118870, d120310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20141 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d118749 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d118871 q = 1) (hb : d120311 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118871, d120311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d118871, d120311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d118873 q = 1) (hb : d120313 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118873, d120313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20145 q ha hb
    | true =>
      simp only [d118873, d120313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118874 q = 1) (hb : d120314 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118874, d120314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118874, d120314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d118875 q = 1) (hb : d120315 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118875, d120315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118875, d120315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d118885 q = 1) (hb : d120330 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118885, d120330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118885, d120330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d118886 q = 1) (hb : d120331 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118886, d120331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118886, d120331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d118887 q = 1) (hb : d120332 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118887, d120332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118887, d120332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro20149 (p : Pattern) (ha : d118889 p = 1) (hb : d120334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118639 q = 1) (hb : d120086 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118639, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20100 q ha hb
    | true =>
      simp only [d118639, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118696 q = 1) (hb : d120139 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118696, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118696, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118697 q = 1) (hb : d120140 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118697, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118697, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118698 q = 1) (hb : d120141 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118698, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118698, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118699 q = 1) (hb : d120142 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118699, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118699, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118889 q = 1) (hb : d120334 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118889, d120334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118889, d120334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20150 (p : Pattern) (ha : d118779 p = 1) (hb : d120350 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118774 q = 1) (hb : d120209 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118774, d120209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20123 q ha hb
    | true =>
      simp only [d118774, d120209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20103 q ha hb
  have h2 (q : Pattern) (ha : d118775 q = 1) (hb : d120210 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118775, d120210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118775, d120210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118776 q = 1) (hb : d120211 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118776, d120211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118776, d120211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d118662 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d118777 q = 1) (hb : d120212 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118777, d120212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118777, d120212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d118663 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d118778 q = 1) (hb : d120349 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d118778, d120349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118778, d120349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d118779 q = 1) (hb : d120350 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d118779, d120350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d118779, d120350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20151 (p : Pattern) (ha : d118785 p = 1) (hb : d120360 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118780 q = 1) (hb : d120351 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118780, d120351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20150 q ha hb
    | true =>
      simp only [d118780, d120351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118781 q = 1) (hb : d120352 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118781, d120352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118781, d120352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118666 q = 1) (hb : d120109 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118666, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20104 q ha hb
    | true =>
      simp only [d118666, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118667 q = 1) (hb : d120110 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118667, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118667, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118782 q = 1) (hb : d120357 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118782, d120357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118782, d120357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118783 q = 1) (hb : d120358 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118783, d120358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118783, d120358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d118784 q = 1) (hb : d120359 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118784, d120359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d118784, d120359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d118785 q = 1) (hb : d120360 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118785, d120360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d118785, d120360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20152 (p : Pattern) (ha : d118899 p = 1) (hb : d120340 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d118899 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21071 q = 1) (hb : d118895 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21071, d118895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21071, d118895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20135 q ha hb
  have h3 (q : Pattern) (ha : d20990 q = 1) (hb : d118831 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d118831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20135 q ha hb
    | true =>
      simp only [d20990, d118831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d21072 q = 1) (hb : d118896 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21072, d118896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21072, d118896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20991 q = 1) (hb : d118832 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d118832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20991, d118832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d21073 q = 1) (hb : d118897 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21073, d118897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21073, d118897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21074 q = 1) (hb : d118898 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21074, d118898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21074, d118898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d971 q = 1) (hb : d118769 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d118769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d971, d118769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20112 q ha hb
  have h9 (q : Pattern) (ha : d751 q = 1) (hb : d118716 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d118716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20112 q ha hb
    | true =>
      simp only [d751, d118716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d972 q = 1) (hb : d118770 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d118770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d972, d118770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d752 q = 1) (hb : d118717 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d118717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d752, d118717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d973 q = 1) (hb : d118771 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d118771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d973, d118771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d974 q = 1) (hb : d118772 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d118772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d974, d118772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d21075 q = 1) (hb : d118899 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21075, d118899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21075, d118899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d118899 q = 1) (hb : d120340 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d120340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro20153 (p : Pattern) (ha : d118905 p = 1) (hb : d120346 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118900 q = 1) (hb : d120341 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118900, d120341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20152 q ha hb
    | true =>
      simp only [d118900, d120341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20123 q ha hb
  have h2 (q : Pattern) (ha : d118901 q = 1) (hb : d120342 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118901, d120342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118901, d120342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118902 q = 1) (hb : d120343 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118902, d120343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118902, d120343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d118776 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d118903 q = 1) (hb : d120344 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118903, d120344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118903, d120344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d118774 q = 1) (hb : d120209 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118774, d120209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20123 q ha hb
    | true =>
      simp only [d118774, d120209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20103 q ha hb
  have h7 (q : Pattern) (ha : d118775 q = 1) (hb : d120210 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118775, d120210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118775, d120210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d118776 q = 1) (hb : d120211 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118776, d120211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118776, d120211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d118662 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d118777 q = 1) (hb : d120212 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118777, d120212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d118777, d120212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d118904 q = 1) (hb : d120345 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d118904, d120345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118904, d120345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d118905 q = 1) (hb : d120346 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d118905, d120346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d118905, d120346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro20154 (p : Pattern) (ha : d118911 p = 1) (hb : d120356 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118906 q = 1) (hb : d120347 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118906, d120347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20153 q ha hb
    | true =>
      simp only [d118906, d120347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118907 q = 1) (hb : d120348 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118907, d120348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118907, d120348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118780 q = 1) (hb : d120351 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118780, d120351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20150 q ha hb
    | true =>
      simp only [d118780, d120351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118781 q = 1) (hb : d120352 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118781, d120352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118781, d120352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118908 q = 1) (hb : d120353 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118908, d120353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118908, d120353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118909 q = 1) (hb : d120354 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118909, d120354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118909, d120354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d118910 q = 1) (hb : d120355 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118910, d120355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d118910, d120355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d118911 q = 1) (hb : d120356 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118911, d120356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d118911, d120356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20155 (p : Pattern) (ha : d118917 p = 1) (hb : d120366 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118780 q = 1) (hb : d120215 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118780, d120215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20124 q ha hb
    | true =>
      simp only [d118780, d120215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118781 q = 1) (hb : d120216 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118781, d120216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118781, d120216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118914 q = 1) (hb : d120363 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118914, d120363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118914, d120363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118915 q = 1) (hb : d120364 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118915, d120364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118915, d120364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118916 q = 1) (hb : d120365 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118916, d120365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118916, d120365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d118917 q = 1) (hb : d120366 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118917, d120366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118917, d120366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20156 (p : Pattern) (ha : d118923 p = 1) (hb : d120372 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118912 q = 1) (hb : d120361 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118912, d120361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20154 q ha hb
    | true =>
      simp only [d118912, d120361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20151 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d118786 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d118913 q = 1) (hb : d120362 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118913, d120362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d118913, d120362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d118918 q = 1) (hb : d120367 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118918, d120367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20155 q ha hb
    | true =>
      simp only [d118918, d120367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118919 q = 1) (hb : d120368 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118919, d120368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118919, d120368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d118920 q = 1) (hb : d120369 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118920, d120369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118920, d120369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d118921 q = 1) (hb : d120370 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118921, d120370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118921, d120370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d118922 q = 1) (hb : d120371 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118922, d120371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118922, d120371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d118923 q = 1) (hb : d120372 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118923, d120372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118923, d120372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro20157 (p : Pattern) (ha : d118929 p = 1) (hb : d120378 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118672 q = 1) (hb : d120115 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118672, d120115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20105 q ha hb
    | true =>
      simp only [d118672, d120115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118925 q = 1) (hb : d120374 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118925, d120374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118925, d120374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118926 q = 1) (hb : d120375 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118926, d120375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118926, d120375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118927 q = 1) (hb : d120376 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118927, d120376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118927, d120376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118928 q = 1) (hb : d120377 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118928, d120377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118928, d120377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118929 q = 1) (hb : d120378 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118929, d120378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118929, d120378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20158 (p : Pattern) (ha : d118935 p = 1) (hb : d120384 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118809 q = 1) (hb : d120244 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118809, d120244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118809, d120244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20129 q ha hb
  have h2 (q : Pattern) (ha : d118810 q = 1) (hb : d120245 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118810, d120245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d118810, d120245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d118816 q = 1) (hb : d120251 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118816, d120251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20129 q ha hb
    | true =>
      simp only [d118816, d120251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20130 q ha hb
  have h4 (q : Pattern) (ha : d118817 q = 1) (hb : d120252 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118817, d120252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118817, d120252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118818 q = 1) (hb : d120253 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d118818, d120253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118818, d120253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118879 q = 1) (hb : d120319 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118879, d120319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20140 q ha hb
    | true =>
      simp only [d118879, d120319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20146 q ha hb
  have h7 (q : Pattern) (ha : d118881 q = 1) (hb : d120326 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118881, d120326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20147 q ha hb
    | true =>
      simp only [d118881, d120326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20109 q ha hb
  have h8 (q : Pattern) (ha : d118882 q = 1) (hb : d120327 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118882, d120327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d118882, d120327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d118883 q = 1) (hb : d120328 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d118883, d120328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d118883, d120328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d118884 q = 1) (hb : d120329 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d118884, d120329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118884, d120329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d118888 q = 1) (hb : d120333 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118888, d120333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118888, d120333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20148 q ha hb
  have h12 (q : Pattern) (ha : d118890 q = 1) (hb : d120335 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118890, d120335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118890, d120335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20149 q ha hb
  have h13 (q : Pattern) (ha : d118891 q = 1) (hb : d120336 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118891, d120336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d118891, d120336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d118892 q = 1) (hb : d120337 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d118892, d120337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d118892, d120337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d118893 q = 1) (hb : d120338 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d118893, d120338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d118893, d120338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d118894 q = 1) (hb : d120339 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d118894, d120339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d118894, d120339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d118924 q = 1) (hb : d120373 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118924, d120373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118924, d120373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20156 q ha hb
  have h18 (q : Pattern) (ha : d118930 q = 1) (hb : d120379 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118930, d120379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118930, d120379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20157 q ha hb
  have h19 (q : Pattern) (ha : d118931 q = 1) (hb : d120380 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118931, d120380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d118931, d120380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d118932 q = 1) (hb : d120381 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d118932, d120381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d118932, d120381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d118933 q = 1) (hb : d120382 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d118933, d120382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d118933, d120382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d118934 q = 1) (hb : d120383 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d118934, d120383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d118934, d120383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d118935 q = 1) (hb : d120384 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d118935, d120384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d118935, d120384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro20159 (p : Pattern) (ha : d118941 p = 1) (hb : d120390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118936 q = 1) (hb : d120385 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d118936, d120385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118936, d120385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20158 q ha hb
  have h2 (q : Pattern) (ha : d118937 q = 1) (hb : d120386 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d118937, d120386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118937, d120386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118938 q = 1) (hb : d120387 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d118938, d120387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118938, d120387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d118939 q = 1) (hb : d120388 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d118939, d120388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118939, d120388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118940 q = 1) (hb : d120389 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d118940, d120389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118940, d120389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118941 q = 1) (hb : d120390 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d118941, d120390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118941, d120390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20160 (p : Pattern) (ha : d118943 p = 1) (hb : d120392 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d118943 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d751 q = 1) (hb : d118716 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d118716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20112 q ha hb
    | true =>
      simp only [d751, d118716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d752 q = 1) (hb : d118717 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d118717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d752, d118717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d753 q = 1) (hb : d118718 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d118718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d753, d118718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d754 q = 1) (hb : d118719 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d118719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d754, d118719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d757 q = 1) (hb : d118943 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d118943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d757, d118943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d118943 q = 1) (hb : d120392 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d120392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro20161 (p : Pattern) (ha : d118953 p = 1) (hb : d120402 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118944 q = 1) (hb : d120393 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118944, d120393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20136 q ha hb
    | true =>
      simp only [d118944, d120393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20160 q ha hb
  have h2 (q : Pattern) (ha : d118945 q = 1) (hb : d120394 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118945, d120394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118945, d120394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118946 q = 1) (hb : d120395 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118946, d120395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118946, d120395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d118949 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d118950 q = 1) (hb : d120396 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118950, d120396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118950, d120396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d118947 q = 1) (hb : d120397 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118947, d120397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20160 q ha hb
    | true =>
      simp only [d118947, d120397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d118948 q = 1) (hb : d120398 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118948, d120398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118948, d120398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d118949 q = 1) (hb : d120399 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118949, d120399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118949, d120399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d118951 q = 1) (hb : d120400 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118951, d120400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d118951, d120400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d118952 q = 1) (hb : d120401 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d118952, d120401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118952, d120401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d118953 q = 1) (hb : d120402 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d118953, d120402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d118953, d120402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro20162 (p : Pattern) (ha : d118957 p = 1) (hb : d120406 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118947 q = 1) (hb : d120397 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118947, d120397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20160 q ha hb
    | true =>
      simp only [d118947, d120397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118948 q = 1) (hb : d120398 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118948, d120398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118948, d120398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118949 q = 1) (hb : d120399 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118949, d120399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118949, d120399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d118951 q = 1) (hb : d120400 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118951, d120400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118951, d120400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118956 q = 1) (hb : d120405 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d118956, d120405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118956, d120405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d118957 q = 1) (hb : d120406 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d118957, d120406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118957, d120406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20163 (p : Pattern) (ha : d118963 p = 1) (hb : d120412 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118954 q = 1) (hb : d120403 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118954, d120403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20161 q ha hb
    | true =>
      simp only [d118954, d120403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118955 q = 1) (hb : d120404 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118955, d120404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118955, d120404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118958 q = 1) (hb : d120407 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118958, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20162 q ha hb
    | true =>
      simp only [d118958, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118959 q = 1) (hb : d120408 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118959, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118959, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118960 q = 1) (hb : d120409 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118960, d120409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118960, d120409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118961 q = 1) (hb : d120410 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118961, d120410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118961, d120410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d118962 q = 1) (hb : d120411 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118962, d120411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d118962, d120411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d118963 q = 1) (hb : d120412 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118963, d120412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118963, d120412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20164 (p : Pattern) (ha : d118967 p = 1) (hb : d120416 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118958 q = 1) (hb : d120407 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118958, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20162 q ha hb
    | true =>
      simp only [d118958, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118959 q = 1) (hb : d120408 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118959, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118959, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118964 q = 1) (hb : d120413 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118964, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118964, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118965 q = 1) (hb : d120414 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118965, d120414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118965, d120414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118966 q = 1) (hb : d120415 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118966, d120415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118966, d120415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d118967 q = 1) (hb : d120416 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118967, d120416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118967, d120416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20165 (p : Pattern) (ha : d118973 p = 1) (hb : d120422 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118968 q = 1) (hb : d120417 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118968, d120417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20163 q ha hb
    | true =>
      simp only [d118968, d120417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20164 q ha hb
  have h2 (q : Pattern) (ha : d118969 q = 1) (hb : d120418 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118969, d120418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118969, d120418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118970 q = 1) (hb : d120419 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118970, d120419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118970, d120419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118971 q = 1) (hb : d120420 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118971, d120420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118971, d120420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118972 q = 1) (hb : d120421 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118972, d120421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118972, d120421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118973 q = 1) (hb : d120422 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118973, d120422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118973, d120422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20166 (p : Pattern) (ha : d118976 p = 1) (hb : d120425 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118954 q = 1) (hb : d120403 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118954, d120403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20161 q ha hb
    | true =>
      simp only [d118954, d120403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118955 q = 1) (hb : d120404 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118955, d120404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118955, d120404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118958 q = 1) (hb : d120407 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118958, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20162 q ha hb
    | true =>
      simp only [d118958, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118959 q = 1) (hb : d120408 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118959, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118959, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118960 q = 1) (hb : d120409 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118960, d120409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118960, d120409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118961 q = 1) (hb : d120410 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118961, d120410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118961, d120410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d118962 q = 1) (hb : d120411 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118962, d120411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d118962, d120411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d118976 q = 1) (hb : d120425 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118976, d120425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d118976, d120425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20167 (p : Pattern) (ha : d118977 p = 1) (hb : d120426 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118958 q = 1) (hb : d120407 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118958, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20162 q ha hb
    | true =>
      simp only [d118958, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118959 q = 1) (hb : d120408 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118959, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118959, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118964 q = 1) (hb : d120413 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118964, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118964, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118965 q = 1) (hb : d120414 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118965, d120414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118965, d120414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118966 q = 1) (hb : d120415 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118966, d120415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118966, d120415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d118977 q = 1) (hb : d120426 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118977, d120426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118977, d120426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20168 (p : Pattern) (ha : d118983 p = 1) (hb : d120432 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118968 q = 1) (hb : d120417 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118968, d120417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20163 q ha hb
    | true =>
      simp only [d118968, d120417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20164 q ha hb
  have h2 (q : Pattern) (ha : d118969 q = 1) (hb : d120418 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118969, d120418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118969, d120418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118970 q = 1) (hb : d120419 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118970, d120419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118970, d120419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118971 q = 1) (hb : d120420 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118971, d120420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118971, d120420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118972 q = 1) (hb : d120421 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118972, d120421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118972, d120421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118978 q = 1) (hb : d120427 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118978, d120427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20166 q ha hb
    | true =>
      simp only [d118978, d120427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20167 q ha hb
  have h7 (q : Pattern) (ha : d118979 q = 1) (hb : d120428 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118979, d120428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118979, d120428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d118980 q = 1) (hb : d120429 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118980, d120429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d118980, d120429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d118981 q = 1) (hb : d120430 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118981, d120430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118981, d120430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d118982 q = 1) (hb : d120431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118982, d120431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118982, d120431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d118983 q = 1) (hb : d120432 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118983, d120432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118983, d120432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro20169 (p : Pattern) (ha : d118953 p = 1) (hb : d120463 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118944 q = 1) (hb : d120393 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118944, d120393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20136 q ha hb
    | true =>
      simp only [d118944, d120393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20160 q ha hb
  have h2 (q : Pattern) (ha : d118945 q = 1) (hb : d120394 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118945, d120394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118945, d120394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118946 q = 1) (hb : d120395 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118946, d120395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118946, d120395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d118949 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d118950 q = 1) (hb : d120396 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118950, d120396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118950, d120396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d118951 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d118952 q = 1) (hb : d120462 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d118952, d120462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118952, d120462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d118953 q = 1) (hb : d120463 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d118953, d120463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d118953, d120463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20170 (p : Pattern) (ha : d118963 p = 1) (hb : d120473 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118954 q = 1) (hb : d120464 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118954, d120464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20169 q ha hb
    | true =>
      simp only [d118954, d120464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118955 q = 1) (hb : d120465 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118955, d120465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118955, d120465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118958 q = 1) (hb : d120407 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118958, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20162 q ha hb
    | true =>
      simp only [d118958, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118959 q = 1) (hb : d120408 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118959, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118959, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118960 q = 1) (hb : d120470 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118960, d120470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118960, d120470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118961 q = 1) (hb : d120471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118961, d120471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118961, d120471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d118962 q = 1) (hb : d120472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118962, d120472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d118962, d120472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d118963 q = 1) (hb : d120473 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118963, d120473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118963, d120473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20171 (p : Pattern) (ha : d118988 p = 1) (hb : d120437 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118954 q = 1) (hb : d120403 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118954, d120403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20161 q ha hb
    | true =>
      simp only [d118954, d120403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118955 q = 1) (hb : d120404 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118955, d120404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118955, d120404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118958 q = 1) (hb : d120407 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118958, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20162 q ha hb
    | true =>
      simp only [d118958, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118959 q = 1) (hb : d120408 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118959, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118959, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118960 q = 1) (hb : d120409 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118960, d120409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118960, d120409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118961 q = 1) (hb : d120410 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118961, d120410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118961, d120410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d118987 q = 1) (hb : d120436 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118987, d120436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118987, d120436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d118988 q = 1) (hb : d120437 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118988, d120437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118988, d120437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20172 (p : Pattern) (ha : d118990 p = 1) (hb : d120439 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118958 q = 1) (hb : d120407 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118958, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20162 q ha hb
    | true =>
      simp only [d118958, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118959 q = 1) (hb : d120408 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118959, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118959, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118964 q = 1) (hb : d120413 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118964, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118964, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118965 q = 1) (hb : d120414 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118965, d120414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118965, d120414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118989 q = 1) (hb : d120438 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118989, d120438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118989, d120438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118990 q = 1) (hb : d120439 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118990, d120439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118990, d120439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20173 (p : Pattern) (ha : d118997 p = 1) (hb : d120446 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118954 q = 1) (hb : d120403 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118954, d120403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20161 q ha hb
    | true =>
      simp only [d118954, d120403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118955 q = 1) (hb : d120404 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118955, d120404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118955, d120404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118958 q = 1) (hb : d120407 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118958, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20162 q ha hb
    | true =>
      simp only [d118958, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118959 q = 1) (hb : d120408 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118959, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118959, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118960 q = 1) (hb : d120409 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118960, d120409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118960, d120409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118995 q = 1) (hb : d120444 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118995, d120444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118995, d120444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d118996 q = 1) (hb : d120445 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118996, d120445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d118996, d120445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d118997 q = 1) (hb : d120446 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118997, d120446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118997, d120446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20174 (p : Pattern) (ha : d119000 p = 1) (hb : d120449 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118958 q = 1) (hb : d120407 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118958, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20162 q ha hb
    | true =>
      simp only [d118958, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118959 q = 1) (hb : d120408 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118959, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118959, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118964 q = 1) (hb : d120413 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118964, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118964, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118998 q = 1) (hb : d120447 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118998, d120447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118998, d120447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118999 q = 1) (hb : d120448 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118999, d120448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118999, d120448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119000 q = 1) (hb : d120449 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119000, d120449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119000, d120449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20175 (p : Pattern) (ha : d21182 p = 1) (hb : d52288 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d531 q = 1) (hb : d52278 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d52278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74 q ha hb
    | true =>
      simp only [d531, d52278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d532 q = 1) (hb : d52279 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d52279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d532, d52279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d313 q = 1) (hb : d52112 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d52112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41 q ha hb
    | true =>
      simp only [d313, d52112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d314 q = 1) (hb : d52113 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d52113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d314, d52113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d533 q = 1) (hb : d52280 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d533, d52280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d533, d52280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d537 q = 1) (hb : d52284 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d537, d52284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75 q ha hb
    | true =>
      simp only [d537, d52284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d538 q = 1) (hb : d52285 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d538, d52285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d538, d52285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d133 q = 1) (hb : d51984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18 q ha hb
    | true =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d134 q = 1) (hb : d51985 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d539 q = 1) (hb : d52286 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d539, d52286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d539, d52286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d540 q = 1) (hb : d52287 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d540, d52287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d540, d52287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d541 q = 1) (hb : d52288 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d541, d52288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d541, d52288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d52288 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d21182 q = 1) (hb : d52288 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d21182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro20176 (p : Pattern) (ha : d119008 p = 1) (hb : d120453 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d119008 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21183 q = 1) (hb : d119004 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21183, d119004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20175 q ha hb
    | true =>
      simp only [d21183, d119004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21184 q = 1) (hb : d119005 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21184, d119005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21184, d119005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d21185 q = 1) (hb : d119006 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21185, d119006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21185, d119006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21186 q = 1) (hb : d119007 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21186, d119007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21186, d119007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d20990 q = 1) (hb : d118831 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d118831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20135 q ha hb
    | true =>
      simp only [d20990, d118831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d20991 q = 1) (hb : d118832 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d118832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20991, d118832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d20992 q = 1) (hb : d118833 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d20992, d118833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20992, d118833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20993 q = 1) (hb : d118834 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d20993, d118834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20993, d118834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d21187 q = 1) (hb : d119008 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21187, d119008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21187, d119008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d119008 q = 1) (hb : d120453 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d120453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro20177 (p : Pattern) (ha : d119022 p = 1) (hb : d120459 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119009 q = 1) (hb : d120454 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119009, d120454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20176 q ha hb
    | true =>
      simp only [d119009, d120454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20136 q ha hb
  have h2 (q : Pattern) (ha : d119010 q = 1) (hb : d120455 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119010, d120455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119010, d120455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119011 q = 1) (hb : d120456 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119011, d120456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119011, d120456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d119019 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d119020 q = 1) (hb : d120457 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119020, d120457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119020, d120457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d118944 q = 1) (hb : d120393 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118944, d120393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20136 q ha hb
    | true =>
      simp only [d118944, d120393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20160 q ha hb
  have h7 (q : Pattern) (ha : d118945 q = 1) (hb : d120394 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118945, d120394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118945, d120394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d118946 q = 1) (hb : d120395 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118946, d120395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118946, d120395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d118949 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d118950 q = 1) (hb : d120396 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118950, d120396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d118950, d120396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d119021 q = 1) (hb : d120458 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d119021, d120458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119021, d120458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d119022 q = 1) (hb : d120459 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d119022, d120459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d119022, d120459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro20178 (p : Pattern) (ha : d119028 p = 1) (hb : d120469 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119023 q = 1) (hb : d120460 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119023, d120460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20177 q ha hb
    | true =>
      simp only [d119023, d120460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119024 q = 1) (hb : d120461 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119024, d120461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119024, d120461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118954 q = 1) (hb : d120464 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118954, d120464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20169 q ha hb
    | true =>
      simp only [d118954, d120464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118955 q = 1) (hb : d120465 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118955, d120465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118955, d120465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119025 q = 1) (hb : d120466 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119025, d120466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119025, d120466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119026 q = 1) (hb : d120467 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119026, d120467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119026, d120467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119027 q = 1) (hb : d120468 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119027, d120468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119027, d120468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119028 q = 1) (hb : d120469 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119028, d120469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119028, d120469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20179 (p : Pattern) (ha : d119034 p = 1) (hb : d120479 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118954 q = 1) (hb : d120403 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118954, d120403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20161 q ha hb
    | true =>
      simp only [d118954, d120403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118955 q = 1) (hb : d120404 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118955, d120404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118955, d120404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119031 q = 1) (hb : d120476 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119031, d120476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119031, d120476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119032 q = 1) (hb : d120477 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119032, d120477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119032, d120477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119033 q = 1) (hb : d120478 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119033, d120478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119033, d120478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119034 q = 1) (hb : d120479 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119034, d120479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119034, d120479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20180 (p : Pattern) (ha : d119040 p = 1) (hb : d120485 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118991 q = 1) (hb : d120440 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118991, d120440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20171 q ha hb
    | true =>
      simp only [d118991, d120440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20172 q ha hb
  have h2 (q : Pattern) (ha : d118992 q = 1) (hb : d120441 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118992, d120441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118992, d120441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118993 q = 1) (hb : d120442 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118993, d120442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118993, d120442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118994 q = 1) (hb : d120443 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118994, d120443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118994, d120443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119001 q = 1) (hb : d120450 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119001, d120450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20173 q ha hb
    | true =>
      simp only [d119001, d120450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20174 q ha hb
  have h6 (q : Pattern) (ha : d119002 q = 1) (hb : d120451 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119002, d120451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119002, d120451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d119003 q = 1) (hb : d120452 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119003, d120452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119003, d120452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119029 q = 1) (hb : d120474 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119029, d120474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20178 q ha hb
    | true =>
      simp only [d119029, d120474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20170 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d118968 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d119030 q = 1) (hb : d120475 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119030, d120475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d119030, d120475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d119035 q = 1) (hb : d120480 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119035, d120480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20179 q ha hb
    | true =>
      simp only [d119035, d120480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d119036 q = 1) (hb : d120481 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119036, d120481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d119036, d120481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d119037 q = 1) (hb : d120482 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119037, d120482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d119037, d120482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d119038 q = 1) (hb : d120483 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119038, d120483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119038, d120483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d119039 q = 1) (hb : d120484 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119039, d120484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119039, d120484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d119040 q = 1) (hb : d120485 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119040, d120485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119040, d120485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro20181 (p : Pattern) (ha : d118976 p = 1) (hb : d120498 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118954 q = 1) (hb : d120464 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118954, d120464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20169 q ha hb
    | true =>
      simp only [d118954, d120464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118955 q = 1) (hb : d120465 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118955, d120465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118955, d120465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118958 q = 1) (hb : d120407 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118958, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20162 q ha hb
    | true =>
      simp only [d118958, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118959 q = 1) (hb : d120408 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118959, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118959, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118960 q = 1) (hb : d120470 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118960, d120470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118960, d120470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118961 q = 1) (hb : d120471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118961, d120471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118961, d120471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d118962 q = 1) (hb : d120472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118962, d120472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d118962, d120472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d118976 q = 1) (hb : d120498 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118976, d120498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d118976, d120498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20182 (p : Pattern) (ha : d119041 p = 1) (hb : d120486 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118954 q = 1) (hb : d120403 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118954, d120403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20161 q ha hb
    | true =>
      simp only [d118954, d120403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118955 q = 1) (hb : d120404 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118955, d120404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118955, d120404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118958 q = 1) (hb : d120407 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118958, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20162 q ha hb
    | true =>
      simp only [d118958, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118959 q = 1) (hb : d120408 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118959, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118959, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118960 q = 1) (hb : d120409 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118960, d120409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118960, d120409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118961 q = 1) (hb : d120410 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118961, d120410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118961, d120410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d118987 q = 1) (hb : d120436 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118987, d120436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118987, d120436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119041 q = 1) (hb : d120486 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119041, d120486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119041, d120486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20183 (p : Pattern) (ha : d119042 p = 1) (hb : d120487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118958 q = 1) (hb : d120407 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118958, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20162 q ha hb
    | true =>
      simp only [d118958, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118959 q = 1) (hb : d120408 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118959, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118959, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118964 q = 1) (hb : d120413 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118964, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118964, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118965 q = 1) (hb : d120414 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118965, d120414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118965, d120414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118989 q = 1) (hb : d120438 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118989, d120438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118989, d120438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119042 q = 1) (hb : d120487 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119042, d120487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119042, d120487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20184 (p : Pattern) (ha : d119047 p = 1) (hb : d120492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118954 q = 1) (hb : d120403 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118954, d120403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20161 q ha hb
    | true =>
      simp only [d118954, d120403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118955 q = 1) (hb : d120404 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118955, d120404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118955, d120404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118958 q = 1) (hb : d120407 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118958, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20162 q ha hb
    | true =>
      simp only [d118958, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118959 q = 1) (hb : d120408 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118959, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118959, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118960 q = 1) (hb : d120409 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118960, d120409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118960, d120409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118995 q = 1) (hb : d120444 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118995, d120444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118995, d120444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d118996 q = 1) (hb : d120445 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118996, d120445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d118996, d120445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119047 q = 1) (hb : d120492 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119047, d120492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119047, d120492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20185 (p : Pattern) (ha : d119048 p = 1) (hb : d120493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118958 q = 1) (hb : d120407 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118958, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20162 q ha hb
    | true =>
      simp only [d118958, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118959 q = 1) (hb : d120408 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118959, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118959, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118964 q = 1) (hb : d120413 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118964, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118964, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118998 q = 1) (hb : d120447 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118998, d120447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118998, d120447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118999 q = 1) (hb : d120448 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118999, d120448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118999, d120448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119048 q = 1) (hb : d120493 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119048, d120493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119048, d120493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20186 (p : Pattern) (ha : d119052 p = 1) (hb : d120497 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119023 q = 1) (hb : d120460 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119023, d120460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20177 q ha hb
    | true =>
      simp only [d119023, d120460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119024 q = 1) (hb : d120461 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119024, d120461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119024, d120461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118954 q = 1) (hb : d120464 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118954, d120464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20169 q ha hb
    | true =>
      simp only [d118954, d120464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118955 q = 1) (hb : d120465 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118955, d120465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118955, d120465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119025 q = 1) (hb : d120466 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119025, d120466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119025, d120466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119026 q = 1) (hb : d120467 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119026, d120467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119026, d120467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119027 q = 1) (hb : d120468 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119027, d120468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119027, d120468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119052 q = 1) (hb : d120497 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119052, d120497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119052, d120497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20187 (p : Pattern) (ha : d119055 p = 1) (hb : d120501 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118954 q = 1) (hb : d120403 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118954, d120403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20161 q ha hb
    | true =>
      simp only [d118954, d120403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118955 q = 1) (hb : d120404 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118955, d120404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118955, d120404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119031 q = 1) (hb : d120476 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119031, d120476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119031, d120476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119032 q = 1) (hb : d120477 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119032, d120477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119032, d120477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119033 q = 1) (hb : d120478 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119033, d120478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119033, d120478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119055 q = 1) (hb : d120501 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119055, d120501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119055, d120501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20188 (p : Pattern) (ha : d119061 p = 1) (hb : d120507 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118991 q = 1) (hb : d120440 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118991, d120440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20171 q ha hb
    | true =>
      simp only [d118991, d120440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20172 q ha hb
  have h2 (q : Pattern) (ha : d118992 q = 1) (hb : d120441 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118992, d120441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118992, d120441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118993 q = 1) (hb : d120442 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118993, d120442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118993, d120442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118994 q = 1) (hb : d120443 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118994, d120443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118994, d120443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119001 q = 1) (hb : d120450 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119001, d120450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20173 q ha hb
    | true =>
      simp only [d119001, d120450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20174 q ha hb
  have h6 (q : Pattern) (ha : d119002 q = 1) (hb : d120451 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119002, d120451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119002, d120451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d119003 q = 1) (hb : d120452 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119003, d120452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119003, d120452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119029 q = 1) (hb : d120474 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119029, d120474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20178 q ha hb
    | true =>
      simp only [d119029, d120474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20170 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d118968 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d119030 q = 1) (hb : d120475 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119030, d120475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d119030, d120475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d119035 q = 1) (hb : d120480 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119035, d120480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20179 q ha hb
    | true =>
      simp only [d119035, d120480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d119036 q = 1) (hb : d120481 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119036, d120481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d119036, d120481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d119037 q = 1) (hb : d120482 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119037, d120482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d119037, d120482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d119038 q = 1) (hb : d120483 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119038, d120483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119038, d120483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d119039 q = 1) (hb : d120484 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119039, d120484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119039, d120484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d119043 q = 1) (hb : d120488 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119043, d120488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20182 q ha hb
    | true =>
      simp only [d119043, d120488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20183 q ha hb
  have h17 (q : Pattern) (ha : d119044 q = 1) (hb : d120489 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119044, d120489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119044, d120489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d119045 q = 1) (hb : d120490 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119045, d120490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d119045, d120490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d119046 q = 1) (hb : d120491 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119046, d120491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119046, d120491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d119049 q = 1) (hb : d120494 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119049, d120494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20184 q ha hb
    | true =>
      simp only [d119049, d120494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20185 q ha hb
  have h21 (q : Pattern) (ha : d119050 q = 1) (hb : d120495 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119050, d120495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119050, d120495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d119051 q = 1) (hb : d120496 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119051, d120496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d119051, d120496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d119053 q = 1) (hb : d120499 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119053, d120499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20186 q ha hb
    | true =>
      simp only [d119053, d120499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20181 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d118978 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d119054 q = 1) (hb : d120500 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119054, d120500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d119054, d120500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d119056 q = 1) (hb : d120502 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119056, d120502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20187 q ha hb
    | true =>
      simp only [d119056, d120502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d119057 q = 1) (hb : d120503 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119057, d120503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d119057, d120503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d119058 q = 1) (hb : d120504 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119058, d120504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d119058, d120504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d119059 q = 1) (hb : d120505 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119059, d120505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d119059, d120505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d119060 q = 1) (hb : d120506 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119060, d120506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d119060, d120506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d119061 q = 1) (hb : d120507 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119061, d120507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d119061, d120507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro20189 (p : Pattern) (ha : d119068 p = 1) (hb : d120519 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118968 q = 1) (hb : d120509 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118968, d120509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20170 q ha hb
    | true =>
      simp only [d118968, d120509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20164 q ha hb
  have h2 (q : Pattern) (ha : d118969 q = 1) (hb : d120510 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118969, d120510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118969, d120510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118970 q = 1) (hb : d120511 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118970, d120511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118970, d120511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118971 q = 1) (hb : d120512 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118971, d120512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118971, d120512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118972 q = 1) (hb : d120513 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118972, d120513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118972, d120513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119063 q = 1) (hb : d120514 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119063, d120514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20164 q ha hb
    | true =>
      simp only [d119063, d120514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119064 q = 1) (hb : d120515 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119064, d120515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119064, d120515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119065 q = 1) (hb : d120516 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119065, d120516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119065, d120516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d119066 q = 1) (hb : d120517 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119066, d120517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119066, d120517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d119067 q = 1) (hb : d120518 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119067, d120518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119067, d120518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d119068 q = 1) (hb : d120519 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119068, d120519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119068, d120519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro20190 (p : Pattern) (ha : d119074 p = 1) (hb : d120525 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119063 q = 1) (hb : d120514 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119063, d120514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20164 q ha hb
    | true =>
      simp only [d119063, d120514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119064 q = 1) (hb : d120515 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119064, d120515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119064, d120515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119065 q = 1) (hb : d120516 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119065, d120516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119065, d120516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119066 q = 1) (hb : d120517 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119066, d120517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119066, d120517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119067 q = 1) (hb : d120518 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119067, d120518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119067, d120518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119069 q = 1) (hb : d120520 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119069, d120520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20167 q ha hb
    | true =>
      simp only [d119069, d120520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119070 q = 1) (hb : d120521 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119070, d120521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119070, d120521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119071 q = 1) (hb : d120522 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119071, d120522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119071, d120522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d119072 q = 1) (hb : d120523 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119072, d120523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119072, d120523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d119073 q = 1) (hb : d120524 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119073, d120524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119073, d120524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d119074 q = 1) (hb : d120525 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119074, d120525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119074, d120525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro20191 (p : Pattern) (ha : d119081 p = 1) (hb : d120532 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119053 q = 1) (hb : d120499 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119053, d120499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20186 q ha hb
    | true =>
      simp only [d119053, d120499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20181 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d118978 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d119054 q = 1) (hb : d120500 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119054, d120500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d119054, d120500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d119056 q = 1) (hb : d120502 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119056, d120502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20187 q ha hb
    | true =>
      simp only [d119056, d120502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119057 q = 1) (hb : d120503 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119057, d120503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119057, d120503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119058 q = 1) (hb : d120504 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119058, d120504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119058, d120504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d119079 q = 1) (hb : d120530 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119079, d120530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119079, d120530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119080 q = 1) (hb : d120531 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119080, d120531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119080, d120531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d119081 q = 1) (hb : d120532 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119081, d120532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119081, d120532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro20192 (p : Pattern) (ha : d119083 p = 1) (hb : d120534 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119069 q = 1) (hb : d120520 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119069, d120520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20167 q ha hb
    | true =>
      simp only [d119069, d120520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119070 q = 1) (hb : d120521 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119070, d120521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119070, d120521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119071 q = 1) (hb : d120522 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119071, d120522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119071, d120522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119072 q = 1) (hb : d120523 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119072, d120523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119072, d120523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119073 q = 1) (hb : d120524 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119073, d120524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119073, d120524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119083 q = 1) (hb : d120534 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119083, d120534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119083, d120534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20193 (p : Pattern) (ha : d119093 p = 1) (hb : d120540 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d119093 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21309 q = 1) (hb : d119089 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21309, d119089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21309, d119089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20175 q ha hb
  have h3 (q : Pattern) (ha : d21183 q = 1) (hb : d119004 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21183, d119004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20175 q ha hb
    | true =>
      simp only [d21183, d119004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d21310 q = 1) (hb : d119090 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21310, d119090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21310, d119090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21184 q = 1) (hb : d119005 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21184, d119005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21184, d119005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d21311 q = 1) (hb : d119091 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21311, d119091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21311, d119091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21312 q = 1) (hb : d119092 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21312, d119092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21312, d119092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d21071 q = 1) (hb : d118895 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21071, d118895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21071, d118895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20135 q ha hb
  have h9 (q : Pattern) (ha : d20990 q = 1) (hb : d118831 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d118831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20135 q ha hb
    | true =>
      simp only [d20990, d118831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d21072 q = 1) (hb : d118896 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21072, d118896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21072, d118896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d20991 q = 1) (hb : d118832 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d118832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20991, d118832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d21073 q = 1) (hb : d118897 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21073, d118897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21073, d118897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21074 q = 1) (hb : d118898 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21074, d118898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21074, d118898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d21313 q = 1) (hb : d119093 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21313, d119093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21313, d119093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d119093 q = 1) (hb : d120540 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d120540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro20194 (p : Pattern) (ha : d119106 p = 1) (hb : d120545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d119106 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d971 q = 1) (hb : d118769 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d118769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d971, d118769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20112 q ha hb
  have h3 (q : Pattern) (ha : d751 q = 1) (hb : d118716 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d118716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20112 q ha hb
    | true =>
      simp only [d751, d118716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d972 q = 1) (hb : d118770 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d118770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d972, d118770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d752 q = 1) (hb : d118717 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d118717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d752, d118717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d973 q = 1) (hb : d118771 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d118771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d973, d118771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d974 q = 1) (hb : d118772 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d118772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d974, d118772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d980 q = 1) (hb : d119106 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d119106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d980, d119106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d119106 q = 1) (hb : d120545 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d120545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro20195 (p : Pattern) (ha : d119115 p = 1) (hb : d120551 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119094 q = 1) (hb : d120541 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119094, d120541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20193 q ha hb
    | true =>
      simp only [d119094, d120541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20152 q ha hb
  have h2 (q : Pattern) (ha : d119095 q = 1) (hb : d120542 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119095, d120542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119095, d120542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119096 q = 1) (hb : d120543 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119096, d120543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119096, d120543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d119104 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d119105 q = 1) (hb : d120544 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119105, d120544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119105, d120544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d119107 q = 1) (hb : d120546 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119107, d120546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20152 q ha hb
    | true =>
      simp only [d119107, d120546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20194 q ha hb
  have h7 (q : Pattern) (ha : d119108 q = 1) (hb : d120547 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119108, d120547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119108, d120547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119109 q = 1) (hb : d120548 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119109, d120548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119109, d120548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d119112 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d119113 q = 1) (hb : d120549 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119113, d120549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d119113, d120549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d119114 q = 1) (hb : d120550 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d119114, d120550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119114, d120550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d119115 q = 1) (hb : d120551 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d119115, d120551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d119115, d120551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro20196 (p : Pattern) (ha : d119120 p = 1) (hb : d120555 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119107 q = 1) (hb : d120546 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119107, d120546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20152 q ha hb
    | true =>
      simp only [d119107, d120546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20194 q ha hb
  have h2 (q : Pattern) (ha : d119108 q = 1) (hb : d120547 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119108, d120547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119108, d120547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119109 q = 1) (hb : d120548 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119109, d120548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119109, d120548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d119112 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d119113 q = 1) (hb : d120549 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119113, d120549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119113, d120549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d119118 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d119119 q = 1) (hb : d120554 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d119119, d120554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119119, d120554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d119120 q = 1) (hb : d120555 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d119120, d120555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119120, d120555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20197 (p : Pattern) (ha : d119126 p = 1) (hb : d120561 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119116 q = 1) (hb : d120552 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119116, d120552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20195 q ha hb
    | true =>
      simp only [d119116, d120552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119117 q = 1) (hb : d120553 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119117, d120553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119117, d120553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119121 q = 1) (hb : d120556 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119121, d120556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20196 q ha hb
    | true =>
      simp only [d119121, d120556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119122 q = 1) (hb : d120557 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119122, d120557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119122, d120557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119123 q = 1) (hb : d120558 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119123, d120558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119123, d120558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119124 q = 1) (hb : d120559 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119124, d120559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119124, d120559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119125 q = 1) (hb : d120560 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119125, d120560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119125, d120560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119126 q = 1) (hb : d120561 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119126, d120561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119126, d120561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20198 (p : Pattern) (ha : d119128 p = 1) (hb : d120567 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119110 q = 1) (hb : d120562 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119110, d120562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20194 q ha hb
    | true =>
      simp only [d119110, d120562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119111 q = 1) (hb : d120563 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119111, d120563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119111, d120563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119112 q = 1) (hb : d120564 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119112, d120564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119112, d120564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d119118 q = 1) (hb : d120565 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119118, d120565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119118, d120565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119127 q = 1) (hb : d120566 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d119127, d120566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119127, d120566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119128 q = 1) (hb : d120567 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d119128, d120567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119128, d120567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20199 (p : Pattern) (ha : d119134 p = 1) (hb : d120573 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119121 q = 1) (hb : d120556 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119121, d120556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20196 q ha hb
    | true =>
      simp only [d119121, d120556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119122 q = 1) (hb : d120557 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119122, d120557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119122, d120557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119129 q = 1) (hb : d120568 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119129, d120568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20198 q ha hb
    | true =>
      simp only [d119129, d120568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119130 q = 1) (hb : d120569 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119130, d120569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119130, d120569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119131 q = 1) (hb : d120570 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119131, d120570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119131, d120570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119132 q = 1) (hb : d120571 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119132, d120571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119132, d120571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119133 q = 1) (hb : d120572 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119133, d120572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119133, d120572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119134 q = 1) (hb : d120573 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119134, d120573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119134, d120573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20200 (p : Pattern) (ha : d119120 p = 1) (hb : d120577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119107 q = 1) (hb : d120546 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119107, d120546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20152 q ha hb
    | true =>
      simp only [d119107, d120546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20194 q ha hb
  have h2 (q : Pattern) (ha : d119108 q = 1) (hb : d120547 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119108, d120547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119108, d120547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119109 q = 1) (hb : d120548 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119109, d120548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119109, d120548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d119112 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d119113 q = 1) (hb : d120549 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119113, d120549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119113, d120549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d119110 q = 1) (hb : d120562 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119110, d120562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20194 q ha hb
    | true =>
      simp only [d119110, d120562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119111 q = 1) (hb : d120563 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119111, d120563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119111, d120563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119112 q = 1) (hb : d120564 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119112, d120564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119112, d120564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d119118 q = 1) (hb : d120565 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119118, d120565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d119118, d120565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d119119 q = 1) (hb : d120576 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d119119, d120576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119119, d120576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d119120 q = 1) (hb : d120577 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d119120, d120577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d119120, d120577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro20201 (p : Pattern) (ha : d119145 p = 1) (hb : d120583 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119121 q = 1) (hb : d120578 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119121, d120578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20200 q ha hb
    | true =>
      simp only [d119121, d120578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119122 q = 1) (hb : d120579 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119122, d120579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119122, d120579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119142 q = 1) (hb : d120580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119142, d120580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119142, d120580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119143 q = 1) (hb : d120581 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119143, d120581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119143, d120581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119144 q = 1) (hb : d120582 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119144, d120582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119144, d120582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119145 q = 1) (hb : d120583 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119145, d120583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119145, d120583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20202 (p : Pattern) (ha : d119151 p = 1) (hb : d120589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119135 q = 1) (hb : d120574 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119135, d120574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20197 q ha hb
    | true =>
      simp only [d119135, d120574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20199 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d119140 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d119141 q = 1) (hb : d120575 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119141, d120575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d119141, d120575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d119146 q = 1) (hb : d120584 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119146, d120584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20201 q ha hb
    | true =>
      simp only [d119146, d120584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119147 q = 1) (hb : d120585 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119147, d120585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119147, d120585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119148 q = 1) (hb : d120586 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119148, d120586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119148, d120586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d119149 q = 1) (hb : d120587 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119149, d120587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119149, d120587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119150 q = 1) (hb : d120588 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119150, d120588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119150, d120588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d119151 q = 1) (hb : d120589 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119151, d120589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119151, d120589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro20203 (p : Pattern) (ha : d119139 p = 1) (hb : d120594 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119129 q = 1) (hb : d120568 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119129, d120568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20198 q ha hb
    | true =>
      simp only [d119129, d120568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119130 q = 1) (hb : d120569 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119130, d120569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119130, d120569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119136 q = 1) (hb : d120591 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119136, d120591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119136, d120591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119137 q = 1) (hb : d120592 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119137, d120592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119137, d120592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119138 q = 1) (hb : d120593 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119138, d120593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119138, d120593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119139 q = 1) (hb : d120594 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119139, d120594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119139, d120594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20204 (p : Pattern) (ha : d119158 p = 1) (hb : d120600 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119153 q = 1) (hb : d120595 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119153, d120595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20203 q ha hb
    | true =>
      simp only [d119153, d120595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119154 q = 1) (hb : d120596 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119154, d120596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119154, d120596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119155 q = 1) (hb : d120597 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119155, d120597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119155, d120597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119156 q = 1) (hb : d120598 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119156, d120598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119156, d120598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119157 q = 1) (hb : d120599 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119157, d120599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119157, d120599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119158 q = 1) (hb : d120600 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119158, d120600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119158, d120600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20205 (p : Pattern) (ha : d119164 p = 1) (hb : d120606 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118974 q = 1) (hb : d120423 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118974, d120423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118974, d120423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20165 q ha hb
  have h2 (q : Pattern) (ha : d118975 q = 1) (hb : d120424 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118975, d120424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d118975, d120424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d118984 q = 1) (hb : d120433 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118984, d120433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20165 q ha hb
    | true =>
      simp only [d118984, d120433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20168 q ha hb
  have h4 (q : Pattern) (ha : d118985 q = 1) (hb : d120434 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118985, d120434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118985, d120434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118986 q = 1) (hb : d120435 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d118986, d120435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118986, d120435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119062 q = 1) (hb : d120508 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119062, d120508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20180 q ha hb
    | true =>
      simp only [d119062, d120508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20188 q ha hb
  have h7 (q : Pattern) (ha : d119075 q = 1) (hb : d120526 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119075, d120526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20189 q ha hb
    | true =>
      simp only [d119075, d120526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20190 q ha hb
  have h8 (q : Pattern) (ha : d119076 q = 1) (hb : d120527 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d119076, d120527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119076, d120527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d119077 q = 1) (hb : d120528 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d119077, d120528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d119077, d120528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d119078 q = 1) (hb : d120529 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d119078, d120529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119078, d120529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d119082 q = 1) (hb : d120533 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119082, d120533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119082, d120533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20191 q ha hb
  have h12 (q : Pattern) (ha : d119084 q = 1) (hb : d120535 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119084, d120535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119084, d120535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20192 q ha hb
  have h13 (q : Pattern) (ha : d119085 q = 1) (hb : d120536 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d119085, d120536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d119085, d120536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d119086 q = 1) (hb : d120537 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d119086, d120537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d119086, d120537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d119087 q = 1) (hb : d120538 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d119087, d120538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d119087, d120538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d119088 q = 1) (hb : d120539 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d119088, d120539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d119088, d120539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d119152 q = 1) (hb : d120590 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119152, d120590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119152, d120590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20202 q ha hb
  have h18 (q : Pattern) (ha : d119159 q = 1) (hb : d120601 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119159, d120601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119159, d120601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20204 q ha hb
  have h19 (q : Pattern) (ha : d119160 q = 1) (hb : d120602 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d119160, d120602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d119160, d120602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d119161 q = 1) (hb : d120603 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d119161, d120603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d119161, d120603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d119162 q = 1) (hb : d120604 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d119162, d120604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d119162, d120604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d119163 q = 1) (hb : d120605 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d119163, d120605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d119163, d120605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d119164 q = 1) (hb : d120606 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d119164, d120606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d119164, d120606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro20206 (p : Pattern) (ha : d119170 p = 1) (hb : d120612 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119165 q = 1) (hb : d120607 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d119165, d120607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119165, d120607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20205 q ha hb
  have h2 (q : Pattern) (ha : d119166 q = 1) (hb : d120608 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d119166, d120608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119166, d120608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119167 q = 1) (hb : d120609 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d119167, d120609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119167, d120609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d119168 q = 1) (hb : d120610 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d119168, d120610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119168, d120610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119169 q = 1) (hb : d120611 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d119169, d120611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119169, d120611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119170 q = 1) (hb : d120612 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d119170, d120612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119170, d120612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20207 (p : Pattern) (ha : d21741 p = 1) (hb : d52679 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d1088 q = 1) (hb : d52669 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1088, d52669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74 q ha hb
    | true =>
      simp only [d1088, d52669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro147 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1089 q = 1) (hb : d52670 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1089, d52670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1089, d52670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1094 q = 1) (hb : d52675 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1094, d52675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41 q ha hb
    | true =>
      simp only [d1094, d52675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q ha hb
  have h4 (q : Pattern) (ha : d1095 q = 1) (hb : d52676 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1095, d52676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1095, d52676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d1096 q = 1) (hb : d52677 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1096, d52677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1096, d52677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d537 q = 1) (hb : d52284 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d537, d52284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75 q ha hb
    | true =>
      simp only [d537, d52284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d538 q = 1) (hb : d52285 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d538, d52285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d538, d52285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d133 q = 1) (hb : d51984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18 q ha hb
    | true =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d134 q = 1) (hb : d51985 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d539 q = 1) (hb : d52286 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d539, d52286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d539, d52286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1097 q = 1) (hb : d52678 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1097, d52678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1097, d52678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1098 q = 1) (hb : d52679 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1098, d52679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1098, d52679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d52679 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d21741 q = 1) (hb : d52679 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d21741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro20208 (p : Pattern) (ha : d21754 p = 1) (hb : d52689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d1094 q = 1) (hb : d52675 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1094, d52675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41 q ha hb
    | true =>
      simp only [d1094, d52675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1095 q = 1) (hb : d52676 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1095, d52676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1095, d52676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1104 q = 1) (hb : d52685 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1104, d52685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18 q ha hb
    | true =>
      simp only [d1104, d52685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
  have h4 (q : Pattern) (ha : d1105 q = 1) (hb : d52686 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1105, d52686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1105, d52686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d1106 q = 1) (hb : d52687 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1106, d52687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1106, d52687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d133 q = 1) (hb : d51984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18 q ha hb
    | true =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d134 q = 1) (hb : d51985 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d20 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d135 q = 1) (hb : d51986 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d51986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d135, d51986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1107 q = 1) (hb : d52688 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1107, d52688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1107, d52688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1108 q = 1) (hb : d52689 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1108, d52689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1108, d52689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d52689 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d21754 q = 1) (hb : d52689 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d21754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro20209 (p : Pattern) (ha : d119181 p = 1) (hb : d120615 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d119181 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21742 q = 1) (hb : d119173 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21742, d119173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20207 q ha hb
    | true =>
      simp only [d21742, d119173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21743 q = 1) (hb : d119174 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21743, d119174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21743, d119174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d21744 q = 1) (hb : d119175 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21744, d119175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21744, d119175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21745 q = 1) (hb : d119176 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21745, d119176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21745, d119176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d21755 q = 1) (hb : d119177 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21755, d119177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20208 q ha hb
    | true =>
      simp only [d21755, d119177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d21756 q = 1) (hb : d119178 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21756, d119178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21756, d119178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d21757 q = 1) (hb : d119179 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21757, d119179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21757, d119179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21758 q = 1) (hb : d119180 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21758, d119180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21758, d119180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d21759 q = 1) (hb : d119181 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21759, d119181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21759, d119181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d119181 q = 1) (hb : d120615 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d120615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro20210 (p : Pattern) (ha : d119186 p = 1) (hb : d120616 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d119186 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21755 q = 1) (hb : d119177 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21755, d119177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20208 q ha hb
    | true =>
      simp only [d21755, d119177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21756 q = 1) (hb : d119178 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21756, d119178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21756, d119178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d21757 q = 1) (hb : d119179 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21757, d119179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21757, d119179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21758 q = 1) (hb : d119180 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21758, d119180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21758, d119180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d119185 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d21776 q = 1) (hb : d119186 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21776, d119186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21776, d119186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119186 q = 1) (hb : d120616 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d120616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro20211 (p : Pattern) (ha : d1135 p = 1) (hb : d52700 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1115 q = 1) (hb : d52696 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
  have h2 (q : Pattern) (ha : d1116 q = 1) (hb : d52697 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1116, d52697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1116, d52697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1132 q = 1) (hb : d52698 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1132, d52698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1132, d52698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d51873 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1133 q = 1) (hb : d52699 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1133, d52699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1133, d52699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1134 q = 1) (hb : d52700 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1134, d52700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1134, d52700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52700 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1135 q = 1) (hb : d52700 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro20212 (p : Pattern) (ha : d119190 p = 1) (hb : d120621 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d119190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1136 q = 1) (hb : d119182 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1136, d119182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20211 q ha hb
    | true =>
      simp only [d1136, d119182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1137 q = 1) (hb : d119183 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1137, d119183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1137, d119183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1138 q = 1) (hb : d119184 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1138, d119184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1138, d119184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1139 q = 1) (hb : d119185 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1139, d119185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1139, d119185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1140 q = 1) (hb : d119190 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1140, d119190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1140, d119190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d119190 q = 1) (hb : d120621 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d120621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro20213 (p : Pattern) (ha : d119197 p = 1) (hb : d120627 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119187 q = 1) (hb : d120617 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119187, d120617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20209 q ha hb
    | true =>
      simp only [d119187, d120617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20210 q ha hb
  have h2 (q : Pattern) (ha : d119188 q = 1) (hb : d120618 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119188, d120618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119188, d120618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119189 q = 1) (hb : d120619 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119189, d120619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119189, d120619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d119193 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d119194 q = 1) (hb : d120620 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119194, d120620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119194, d120620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d119191 q = 1) (hb : d120622 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119191, d120622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20210 q ha hb
    | true =>
      simp only [d119191, d120622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20212 q ha hb
  have h7 (q : Pattern) (ha : d119192 q = 1) (hb : d120623 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119192, d120623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119192, d120623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119193 q = 1) (hb : d120624 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119193, d120624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119193, d120624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d119195 q = 1) (hb : d120625 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119195, d120625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d119195, d120625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d119196 q = 1) (hb : d120626 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d119196, d120626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119196, d120626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d119197 q = 1) (hb : d120627 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d119197, d120627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d119197, d120627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro20214 (p : Pattern) (ha : d119201 p = 1) (hb : d120631 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119191 q = 1) (hb : d120622 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119191, d120622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20210 q ha hb
    | true =>
      simp only [d119191, d120622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20212 q ha hb
  have h2 (q : Pattern) (ha : d119192 q = 1) (hb : d120623 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119192, d120623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119192, d120623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119193 q = 1) (hb : d120624 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119193, d120624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119193, d120624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d119195 q = 1) (hb : d120625 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119195, d120625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119195, d120625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119200 q = 1) (hb : d120630 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d119200, d120630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119200, d120630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119201 q = 1) (hb : d120631 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d119201, d120631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119201, d120631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20215 (p : Pattern) (ha : d119207 p = 1) (hb : d120637 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119198 q = 1) (hb : d120628 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119198, d120628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20213 q ha hb
    | true =>
      simp only [d119198, d120628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119199 q = 1) (hb : d120629 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119199, d120629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119199, d120629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119202 q = 1) (hb : d120632 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119202, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20214 q ha hb
    | true =>
      simp only [d119202, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119203 q = 1) (hb : d120633 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119203, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119203, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119204 q = 1) (hb : d120634 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119204, d120634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119204, d120634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119205 q = 1) (hb : d120635 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119205, d120635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119205, d120635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119206 q = 1) (hb : d120636 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119206, d120636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119206, d120636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119207 q = 1) (hb : d120637 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119207, d120637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119207, d120637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20216 (p : Pattern) (ha : d119211 p = 1) (hb : d120641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119202 q = 1) (hb : d120632 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119202, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20214 q ha hb
    | true =>
      simp only [d119202, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119203 q = 1) (hb : d120633 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119203, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119203, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119208 q = 1) (hb : d120638 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119208, d120638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119208, d120638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119209 q = 1) (hb : d120639 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119209, d120639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119209, d120639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119210 q = 1) (hb : d120640 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119210, d120640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119210, d120640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119211 q = 1) (hb : d120641 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119211, d120641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119211, d120641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20217 (p : Pattern) (ha : d119217 p = 1) (hb : d120647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119212 q = 1) (hb : d120642 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119212, d120642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20215 q ha hb
    | true =>
      simp only [d119212, d120642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20216 q ha hb
  have h2 (q : Pattern) (ha : d119213 q = 1) (hb : d120643 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119213, d120643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119213, d120643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119214 q = 1) (hb : d120644 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119214, d120644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119214, d120644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119215 q = 1) (hb : d120645 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119215, d120645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119215, d120645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119216 q = 1) (hb : d120646 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119216, d120646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119216, d120646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119217 q = 1) (hb : d120647 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119217, d120647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119217, d120647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20218 (p : Pattern) (ha : d119220 p = 1) (hb : d120650 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119198 q = 1) (hb : d120628 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119198, d120628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20213 q ha hb
    | true =>
      simp only [d119198, d120628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119199 q = 1) (hb : d120629 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119199, d120629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119199, d120629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119202 q = 1) (hb : d120632 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119202, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20214 q ha hb
    | true =>
      simp only [d119202, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119203 q = 1) (hb : d120633 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119203, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119203, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119204 q = 1) (hb : d120634 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119204, d120634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119204, d120634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119205 q = 1) (hb : d120635 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119205, d120635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119205, d120635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119206 q = 1) (hb : d120636 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119206, d120636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119206, d120636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119220 q = 1) (hb : d120650 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119220, d120650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119220, d120650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20219 (p : Pattern) (ha : d119221 p = 1) (hb : d120651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119202 q = 1) (hb : d120632 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119202, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20214 q ha hb
    | true =>
      simp only [d119202, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119203 q = 1) (hb : d120633 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119203, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119203, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119208 q = 1) (hb : d120638 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119208, d120638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119208, d120638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119209 q = 1) (hb : d120639 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119209, d120639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119209, d120639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119210 q = 1) (hb : d120640 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119210, d120640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119210, d120640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119221 q = 1) (hb : d120651 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119221, d120651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119221, d120651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20220 (p : Pattern) (ha : d119227 p = 1) (hb : d120657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119212 q = 1) (hb : d120642 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119212, d120642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20215 q ha hb
    | true =>
      simp only [d119212, d120642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20216 q ha hb
  have h2 (q : Pattern) (ha : d119213 q = 1) (hb : d120643 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119213, d120643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119213, d120643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119214 q = 1) (hb : d120644 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119214, d120644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119214, d120644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119215 q = 1) (hb : d120645 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119215, d120645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119215, d120645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119216 q = 1) (hb : d120646 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119216, d120646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119216, d120646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119222 q = 1) (hb : d120652 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119222, d120652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20218 q ha hb
    | true =>
      simp only [d119222, d120652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20219 q ha hb
  have h7 (q : Pattern) (ha : d119223 q = 1) (hb : d120653 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119223, d120653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119223, d120653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119224 q = 1) (hb : d120654 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119224, d120654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119224, d120654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d119225 q = 1) (hb : d120655 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119225, d120655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119225, d120655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d119226 q = 1) (hb : d120656 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119226, d120656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119226, d120656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d119227 q = 1) (hb : d120657 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119227, d120657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119227, d120657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro20221 (p : Pattern) (ha : d119197 p = 1) (hb : d120688 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119187 q = 1) (hb : d120617 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119187, d120617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20209 q ha hb
    | true =>
      simp only [d119187, d120617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20210 q ha hb
  have h2 (q : Pattern) (ha : d119188 q = 1) (hb : d120618 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119188, d120618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119188, d120618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119189 q = 1) (hb : d120619 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119189, d120619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119189, d120619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d119193 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d119194 q = 1) (hb : d120620 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119194, d120620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119194, d120620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d119195 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d119196 q = 1) (hb : d120687 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d119196, d120687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119196, d120687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d119197 q = 1) (hb : d120688 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d119197, d120688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119197, d120688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20222 (p : Pattern) (ha : d119207 p = 1) (hb : d120698 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119198 q = 1) (hb : d120689 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119198, d120689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20221 q ha hb
    | true =>
      simp only [d119198, d120689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119199 q = 1) (hb : d120690 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119199, d120690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119199, d120690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119202 q = 1) (hb : d120632 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119202, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20214 q ha hb
    | true =>
      simp only [d119202, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119203 q = 1) (hb : d120633 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119203, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119203, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119204 q = 1) (hb : d120695 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119204, d120695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119204, d120695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119205 q = 1) (hb : d120696 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119205, d120696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119205, d120696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119206 q = 1) (hb : d120697 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119206, d120697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119206, d120697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119207 q = 1) (hb : d120698 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119207, d120698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119207, d120698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20223 (p : Pattern) (ha : d119232 p = 1) (hb : d120662 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119198 q = 1) (hb : d120628 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119198, d120628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20213 q ha hb
    | true =>
      simp only [d119198, d120628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119199 q = 1) (hb : d120629 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119199, d120629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119199, d120629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119202 q = 1) (hb : d120632 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119202, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20214 q ha hb
    | true =>
      simp only [d119202, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119203 q = 1) (hb : d120633 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119203, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119203, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119204 q = 1) (hb : d120634 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119204, d120634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119204, d120634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119205 q = 1) (hb : d120635 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119205, d120635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119205, d120635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119231 q = 1) (hb : d120661 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119231, d120661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119231, d120661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119232 q = 1) (hb : d120662 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119232, d120662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119232, d120662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20224 (p : Pattern) (ha : d119234 p = 1) (hb : d120664 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119202 q = 1) (hb : d120632 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119202, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20214 q ha hb
    | true =>
      simp only [d119202, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119203 q = 1) (hb : d120633 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119203, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119203, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119208 q = 1) (hb : d120638 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119208, d120638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119208, d120638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119209 q = 1) (hb : d120639 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119209, d120639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119209, d120639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119233 q = 1) (hb : d120663 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119233, d120663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119233, d120663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119234 q = 1) (hb : d120664 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119234, d120664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119234, d120664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20225 (p : Pattern) (ha : d119241 p = 1) (hb : d120671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119198 q = 1) (hb : d120628 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119198, d120628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20213 q ha hb
    | true =>
      simp only [d119198, d120628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119199 q = 1) (hb : d120629 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119199, d120629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119199, d120629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119202 q = 1) (hb : d120632 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119202, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20214 q ha hb
    | true =>
      simp only [d119202, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119203 q = 1) (hb : d120633 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119203, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119203, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119204 q = 1) (hb : d120634 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119204, d120634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119204, d120634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119239 q = 1) (hb : d120669 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119239, d120669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119239, d120669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d119240 q = 1) (hb : d120670 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119240, d120670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119240, d120670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119241 q = 1) (hb : d120671 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119241, d120671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119241, d120671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20226 (p : Pattern) (ha : d119244 p = 1) (hb : d120674 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119202 q = 1) (hb : d120632 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119202, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20214 q ha hb
    | true =>
      simp only [d119202, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119203 q = 1) (hb : d120633 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119203, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119203, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119208 q = 1) (hb : d120638 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119208, d120638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119208, d120638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119242 q = 1) (hb : d120672 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119242, d120672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119242, d120672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119243 q = 1) (hb : d120673 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119243, d120673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119243, d120673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119244 q = 1) (hb : d120674 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119244, d120674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119244, d120674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20227 (p : Pattern) (ha : d21736 p = 1) (hb : d52673 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d822 q = 1) (hb : d52499 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d822, d52499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro120 q ha hb
    | true =>
      simp only [d822, d52499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d823 q = 1) (hb : d52500 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d823, d52500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d823, d52500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1088 q = 1) (hb : d52669 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1088, d52669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74 q ha hb
    | true =>
      simp only [d1088, d52669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro147 q ha hb
  have h4 (q : Pattern) (ha : d1089 q = 1) (hb : d52670 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1089, d52670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1089, d52670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1090 q = 1) (hb : d52671 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1090, d52671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1090, d52671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d828 q = 1) (hb : d52505 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d828, d52505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro121 q ha hb
    | true =>
      simp only [d828, d52505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d829 q = 1) (hb : d52506 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d829, d52506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d829, d52506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d537 q = 1) (hb : d52284 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d537, d52284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75 q ha hb
    | true =>
      simp only [d537, d52284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d538 q = 1) (hb : d52285 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d538, d52285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d538, d52285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d830 q = 1) (hb : d52507 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d830, d52507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d830, d52507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1091 q = 1) (hb : d52672 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1091, d52672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1091, d52672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1092 q = 1) (hb : d52673 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1092, d52673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1092, d52673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d52673 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d21736 q = 1) (hb : d52673 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d21736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro20228 (p : Pattern) (ha : d119252 p = 1) (hb : d120678 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d119252 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21737 q = 1) (hb : d119248 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21737, d119248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20227 q ha hb
    | true =>
      simp only [d21737, d119248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21738 q = 1) (hb : d119249 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21738, d119249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21738, d119249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d21739 q = 1) (hb : d119250 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21739, d119250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21739, d119250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21740 q = 1) (hb : d119251 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21740, d119251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21740, d119251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d21742 q = 1) (hb : d119173 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21742, d119173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20207 q ha hb
    | true =>
      simp only [d21742, d119173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d21743 q = 1) (hb : d119174 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21743, d119174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21743, d119174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d21744 q = 1) (hb : d119175 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21744, d119175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21744, d119175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21745 q = 1) (hb : d119176 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21745, d119176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21745, d119176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d21746 q = 1) (hb : d119252 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21746, d119252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21746, d119252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d119252 q = 1) (hb : d120678 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d120678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro20229 (p : Pattern) (ha : d119266 p = 1) (hb : d120684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119253 q = 1) (hb : d120679 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119253, d120679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20228 q ha hb
    | true =>
      simp only [d119253, d120679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20209 q ha hb
  have h2 (q : Pattern) (ha : d119254 q = 1) (hb : d120680 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119254, d120680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119254, d120680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119255 q = 1) (hb : d120681 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119255, d120681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119255, d120681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d119263 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d119264 q = 1) (hb : d120682 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119264, d120682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119264, d120682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d119187 q = 1) (hb : d120617 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119187, d120617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20209 q ha hb
    | true =>
      simp only [d119187, d120617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20210 q ha hb
  have h7 (q : Pattern) (ha : d119188 q = 1) (hb : d120618 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119188, d120618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119188, d120618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119189 q = 1) (hb : d120619 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119189, d120619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119189, d120619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d119193 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d119194 q = 1) (hb : d120620 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119194, d120620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d119194, d120620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d119265 q = 1) (hb : d120683 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d119265, d120683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119265, d120683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d119266 q = 1) (hb : d120684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d119266, d120684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d119266, d120684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro20230 (p : Pattern) (ha : d119272 p = 1) (hb : d120694 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119267 q = 1) (hb : d120685 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119267, d120685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20229 q ha hb
    | true =>
      simp only [d119267, d120685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119268 q = 1) (hb : d120686 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119268, d120686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119268, d120686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119198 q = 1) (hb : d120689 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119198, d120689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20221 q ha hb
    | true =>
      simp only [d119198, d120689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119199 q = 1) (hb : d120690 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119199, d120690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119199, d120690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119269 q = 1) (hb : d120691 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119269, d120691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119269, d120691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119270 q = 1) (hb : d120692 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119270, d120692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119270, d120692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119271 q = 1) (hb : d120693 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119271, d120693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119271, d120693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119272 q = 1) (hb : d120694 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119272, d120694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119272, d120694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20231 (p : Pattern) (ha : d119278 p = 1) (hb : d120704 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119198 q = 1) (hb : d120628 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119198, d120628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20213 q ha hb
    | true =>
      simp only [d119198, d120628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119199 q = 1) (hb : d120629 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119199, d120629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119199, d120629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119275 q = 1) (hb : d120701 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119275, d120701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119275, d120701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119276 q = 1) (hb : d120702 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119276, d120702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119276, d120702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119277 q = 1) (hb : d120703 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119277, d120703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119277, d120703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119278 q = 1) (hb : d120704 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119278, d120704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119278, d120704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20232 (p : Pattern) (ha : d119284 p = 1) (hb : d120710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119235 q = 1) (hb : d120665 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119235, d120665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20223 q ha hb
    | true =>
      simp only [d119235, d120665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20224 q ha hb
  have h2 (q : Pattern) (ha : d119236 q = 1) (hb : d120666 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119236, d120666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119236, d120666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119237 q = 1) (hb : d120667 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119237, d120667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119237, d120667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119238 q = 1) (hb : d120668 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119238, d120668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119238, d120668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119245 q = 1) (hb : d120675 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119245, d120675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20225 q ha hb
    | true =>
      simp only [d119245, d120675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20226 q ha hb
  have h6 (q : Pattern) (ha : d119246 q = 1) (hb : d120676 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119246, d120676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119246, d120676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d119247 q = 1) (hb : d120677 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119247, d120677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119247, d120677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119273 q = 1) (hb : d120699 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119273, d120699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20230 q ha hb
    | true =>
      simp only [d119273, d120699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20222 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d119212 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d119274 q = 1) (hb : d120700 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119274, d120700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d119274, d120700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d119279 q = 1) (hb : d120705 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119279, d120705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20231 q ha hb
    | true =>
      simp only [d119279, d120705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d119280 q = 1) (hb : d120706 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119280, d120706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d119280, d120706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d119281 q = 1) (hb : d120707 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119281, d120707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d119281, d120707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d119282 q = 1) (hb : d120708 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119282, d120708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119282, d120708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d119283 q = 1) (hb : d120709 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119283, d120709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119283, d120709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d119284 q = 1) (hb : d120710 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119284, d120710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119284, d120710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro20233 (p : Pattern) (ha : d119220 p = 1) (hb : d120723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119198 q = 1) (hb : d120689 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119198, d120689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20221 q ha hb
    | true =>
      simp only [d119198, d120689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119199 q = 1) (hb : d120690 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119199, d120690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119199, d120690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119202 q = 1) (hb : d120632 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119202, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20214 q ha hb
    | true =>
      simp only [d119202, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119203 q = 1) (hb : d120633 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119203, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119203, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119204 q = 1) (hb : d120695 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119204, d120695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119204, d120695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119205 q = 1) (hb : d120696 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119205, d120696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119205, d120696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119206 q = 1) (hb : d120697 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119206, d120697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119206, d120697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119220 q = 1) (hb : d120723 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119220, d120723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119220, d120723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20234 (p : Pattern) (ha : d119285 p = 1) (hb : d120711 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119198 q = 1) (hb : d120628 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119198, d120628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20213 q ha hb
    | true =>
      simp only [d119198, d120628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119199 q = 1) (hb : d120629 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119199, d120629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119199, d120629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119202 q = 1) (hb : d120632 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119202, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20214 q ha hb
    | true =>
      simp only [d119202, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119203 q = 1) (hb : d120633 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119203, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119203, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119204 q = 1) (hb : d120634 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119204, d120634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119204, d120634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119205 q = 1) (hb : d120635 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119205, d120635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119205, d120635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119231 q = 1) (hb : d120661 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119231, d120661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119231, d120661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119285 q = 1) (hb : d120711 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119285, d120711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119285, d120711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20235 (p : Pattern) (ha : d119286 p = 1) (hb : d120712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119202 q = 1) (hb : d120632 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119202, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20214 q ha hb
    | true =>
      simp only [d119202, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119203 q = 1) (hb : d120633 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119203, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119203, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119208 q = 1) (hb : d120638 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119208, d120638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119208, d120638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119209 q = 1) (hb : d120639 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119209, d120639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119209, d120639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119233 q = 1) (hb : d120663 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119233, d120663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119233, d120663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119286 q = 1) (hb : d120712 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119286, d120712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119286, d120712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20236 (p : Pattern) (ha : d119291 p = 1) (hb : d120717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119198 q = 1) (hb : d120628 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119198, d120628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20213 q ha hb
    | true =>
      simp only [d119198, d120628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119199 q = 1) (hb : d120629 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119199, d120629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119199, d120629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119202 q = 1) (hb : d120632 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119202, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20214 q ha hb
    | true =>
      simp only [d119202, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119203 q = 1) (hb : d120633 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119203, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119203, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119204 q = 1) (hb : d120634 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119204, d120634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119204, d120634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119239 q = 1) (hb : d120669 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119239, d120669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119239, d120669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d119240 q = 1) (hb : d120670 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119240, d120670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119240, d120670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119291 q = 1) (hb : d120717 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119291, d120717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119291, d120717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20237 (p : Pattern) (ha : d119292 p = 1) (hb : d120718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119202 q = 1) (hb : d120632 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119202, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20214 q ha hb
    | true =>
      simp only [d119202, d120632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119203 q = 1) (hb : d120633 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119203, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119203, d120633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119208 q = 1) (hb : d120638 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119208, d120638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119208, d120638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119242 q = 1) (hb : d120672 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119242, d120672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119242, d120672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119243 q = 1) (hb : d120673 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119243, d120673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119243, d120673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119292 q = 1) (hb : d120718 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119292, d120718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119292, d120718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20238 (p : Pattern) (ha : d119296 p = 1) (hb : d120722 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119267 q = 1) (hb : d120685 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119267, d120685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20229 q ha hb
    | true =>
      simp only [d119267, d120685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119268 q = 1) (hb : d120686 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119268, d120686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119268, d120686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119198 q = 1) (hb : d120689 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119198, d120689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20221 q ha hb
    | true =>
      simp only [d119198, d120689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119199 q = 1) (hb : d120690 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119199, d120690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119199, d120690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119269 q = 1) (hb : d120691 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119269, d120691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119269, d120691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119270 q = 1) (hb : d120692 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119270, d120692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119270, d120692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119271 q = 1) (hb : d120693 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119271, d120693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119271, d120693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119296 q = 1) (hb : d120722 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119296, d120722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119296, d120722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20239 (p : Pattern) (ha : d119299 p = 1) (hb : d120726 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119198 q = 1) (hb : d120628 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119198, d120628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20213 q ha hb
    | true =>
      simp only [d119198, d120628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119199 q = 1) (hb : d120629 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119199, d120629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119199, d120629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119275 q = 1) (hb : d120701 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119275, d120701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119275, d120701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119276 q = 1) (hb : d120702 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119276, d120702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119276, d120702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119277 q = 1) (hb : d120703 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119277, d120703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119277, d120703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119299 q = 1) (hb : d120726 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119299, d120726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119299, d120726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20240 (p : Pattern) (ha : d119305 p = 1) (hb : d120732 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119235 q = 1) (hb : d120665 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119235, d120665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20223 q ha hb
    | true =>
      simp only [d119235, d120665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20224 q ha hb
  have h2 (q : Pattern) (ha : d119236 q = 1) (hb : d120666 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119236, d120666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119236, d120666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119237 q = 1) (hb : d120667 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119237, d120667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119237, d120667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119238 q = 1) (hb : d120668 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119238, d120668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119238, d120668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119245 q = 1) (hb : d120675 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119245, d120675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20225 q ha hb
    | true =>
      simp only [d119245, d120675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20226 q ha hb
  have h6 (q : Pattern) (ha : d119246 q = 1) (hb : d120676 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119246, d120676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119246, d120676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d119247 q = 1) (hb : d120677 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119247, d120677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119247, d120677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119273 q = 1) (hb : d120699 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119273, d120699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20230 q ha hb
    | true =>
      simp only [d119273, d120699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20222 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d119212 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d119274 q = 1) (hb : d120700 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119274, d120700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d119274, d120700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d119279 q = 1) (hb : d120705 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119279, d120705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20231 q ha hb
    | true =>
      simp only [d119279, d120705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d119280 q = 1) (hb : d120706 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119280, d120706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d119280, d120706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d119281 q = 1) (hb : d120707 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119281, d120707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d119281, d120707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d119282 q = 1) (hb : d120708 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119282, d120708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119282, d120708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d119283 q = 1) (hb : d120709 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119283, d120709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119283, d120709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d119287 q = 1) (hb : d120713 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119287, d120713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20234 q ha hb
    | true =>
      simp only [d119287, d120713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20235 q ha hb
  have h17 (q : Pattern) (ha : d119288 q = 1) (hb : d120714 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119288, d120714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119288, d120714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d119289 q = 1) (hb : d120715 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119289, d120715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d119289, d120715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d119290 q = 1) (hb : d120716 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119290, d120716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119290, d120716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d119293 q = 1) (hb : d120719 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119293, d120719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20236 q ha hb
    | true =>
      simp only [d119293, d120719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20237 q ha hb
  have h21 (q : Pattern) (ha : d119294 q = 1) (hb : d120720 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119294, d120720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119294, d120720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d119295 q = 1) (hb : d120721 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119295, d120721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d119295, d120721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d119297 q = 1) (hb : d120724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119297, d120724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20238 q ha hb
    | true =>
      simp only [d119297, d120724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20233 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d119222 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d119298 q = 1) (hb : d120725 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119298, d120725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d119298, d120725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d119300 q = 1) (hb : d120727 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119300, d120727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20239 q ha hb
    | true =>
      simp only [d119300, d120727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d119301 q = 1) (hb : d120728 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119301, d120728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d119301, d120728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d119302 q = 1) (hb : d120729 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119302, d120729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d119302, d120729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d119303 q = 1) (hb : d120730 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119303, d120730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d119303, d120730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d119304 q = 1) (hb : d120731 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119304, d120731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d119304, d120731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d119305 q = 1) (hb : d120732 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119305, d120732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d119305, d120732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro20241 (p : Pattern) (ha : d119312 p = 1) (hb : d120744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119212 q = 1) (hb : d120734 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119212, d120734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20222 q ha hb
    | true =>
      simp only [d119212, d120734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20216 q ha hb
  have h2 (q : Pattern) (ha : d119213 q = 1) (hb : d120735 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119213, d120735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119213, d120735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119214 q = 1) (hb : d120736 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119214, d120736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119214, d120736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119215 q = 1) (hb : d120737 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119215, d120737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119215, d120737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119216 q = 1) (hb : d120738 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119216, d120738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119216, d120738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119307 q = 1) (hb : d120739 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119307, d120739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20216 q ha hb
    | true =>
      simp only [d119307, d120739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119308 q = 1) (hb : d120740 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119308, d120740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119308, d120740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119309 q = 1) (hb : d120741 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119309, d120741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119309, d120741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d119310 q = 1) (hb : d120742 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119310, d120742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119310, d120742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d119311 q = 1) (hb : d120743 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119311, d120743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119311, d120743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d119312 q = 1) (hb : d120744 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119312, d120744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119312, d120744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro20242 (p : Pattern) (ha : d119318 p = 1) (hb : d120750 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119307 q = 1) (hb : d120739 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119307, d120739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20216 q ha hb
    | true =>
      simp only [d119307, d120739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119308 q = 1) (hb : d120740 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119308, d120740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119308, d120740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119309 q = 1) (hb : d120741 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119309, d120741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119309, d120741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119310 q = 1) (hb : d120742 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119310, d120742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119310, d120742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119311 q = 1) (hb : d120743 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119311, d120743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119311, d120743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119313 q = 1) (hb : d120745 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119313, d120745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20219 q ha hb
    | true =>
      simp only [d119313, d120745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119314 q = 1) (hb : d120746 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119314, d120746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119314, d120746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119315 q = 1) (hb : d120747 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119315, d120747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119315, d120747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d119316 q = 1) (hb : d120748 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119316, d120748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119316, d120748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d119317 q = 1) (hb : d120749 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119317, d120749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119317, d120749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d119318 q = 1) (hb : d120750 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119318, d120750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119318, d120750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro20243 (p : Pattern) (ha : d119325 p = 1) (hb : d120757 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119297 q = 1) (hb : d120724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119297, d120724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20238 q ha hb
    | true =>
      simp only [d119297, d120724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20233 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d119222 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d119298 q = 1) (hb : d120725 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119298, d120725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d119298, d120725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d119300 q = 1) (hb : d120727 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119300, d120727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20239 q ha hb
    | true =>
      simp only [d119300, d120727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119301 q = 1) (hb : d120728 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119301, d120728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119301, d120728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119302 q = 1) (hb : d120729 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119302, d120729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119302, d120729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d119323 q = 1) (hb : d120755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119323, d120755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119323, d120755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119324 q = 1) (hb : d120756 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119324, d120756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119324, d120756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d119325 q = 1) (hb : d120757 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119325, d120757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119325, d120757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro20244 (p : Pattern) (ha : d119327 p = 1) (hb : d120759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119313 q = 1) (hb : d120745 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119313, d120745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20219 q ha hb
    | true =>
      simp only [d119313, d120745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119314 q = 1) (hb : d120746 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119314, d120746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119314, d120746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119315 q = 1) (hb : d120747 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119315, d120747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119315, d120747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119316 q = 1) (hb : d120748 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119316, d120748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119316, d120748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119317 q = 1) (hb : d120749 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119317, d120749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119317, d120749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119327 q = 1) (hb : d120759 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119327, d120759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119327, d120759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20245 (p : Pattern) (ha : d119341 p = 1) (hb : d120765 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d119341 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22028 q = 1) (hb : d119333 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22028, d119333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22028, d119333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20227 q ha hb
  have h3 (q : Pattern) (ha : d21737 q = 1) (hb : d119248 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21737, d119248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20227 q ha hb
    | true =>
      simp only [d21737, d119248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d22029 q = 1) (hb : d119334 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22029, d119334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22029, d119334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21738 q = 1) (hb : d119249 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21738, d119249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21738, d119249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d22030 q = 1) (hb : d119335 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22030, d119335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22030, d119335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22031 q = 1) (hb : d119336 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22031, d119336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22031, d119336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d22043 q = 1) (hb : d119337 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22043, d119337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22043, d119337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20207 q ha hb
  have h9 (q : Pattern) (ha : d21742 q = 1) (hb : d119173 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21742, d119173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20207 q ha hb
    | true =>
      simp only [d21742, d119173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d22044 q = 1) (hb : d119338 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22044, d119338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22044, d119338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21743 q = 1) (hb : d119174 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21743, d119174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21743, d119174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d22045 q = 1) (hb : d119339 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22045, d119339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22045, d119339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22046 q = 1) (hb : d119340 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22046, d119340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d22046, d119340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d22047 q = 1) (hb : d119341 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22047, d119341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22047, d119341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d119341 q = 1) (hb : d120765 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d120765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro20246 (p : Pattern) (ha : d119346 p = 1) (hb : d120766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d119346 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22043 q = 1) (hb : d119337 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22043, d119337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22043, d119337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20207 q ha hb
  have h3 (q : Pattern) (ha : d21742 q = 1) (hb : d119173 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21742, d119173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20207 q ha hb
    | true =>
      simp only [d21742, d119173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d22044 q = 1) (hb : d119338 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22044, d119338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22044, d119338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21743 q = 1) (hb : d119174 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21743, d119174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21743, d119174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d22045 q = 1) (hb : d119339 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22045, d119339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22045, d119339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22046 q = 1) (hb : d119340 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22046, d119340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22046, d119340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d22064 q = 1) (hb : d119342 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22064, d119342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22064, d119342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20208 q ha hb
  have h9 (q : Pattern) (ha : d21755 q = 1) (hb : d119177 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21755, d119177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20208 q ha hb
    | true =>
      simp only [d21755, d119177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d22065 q = 1) (hb : d119343 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22065, d119343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22065, d119343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21756 q = 1) (hb : d119178 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21756, d119178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21756, d119178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d22066 q = 1) (hb : d119344 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22066, d119344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22066, d119344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22067 q = 1) (hb : d119345 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22067, d119345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d22067, d119345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d22068 q = 1) (hb : d119346 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22068, d119346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22068, d119346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d119346 q = 1) (hb : d120766 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d120766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro20247 (p : Pattern) (ha : d119363 p = 1) (hb : d120771 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d119363 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22064 q = 1) (hb : d119342 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22064, d119342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22064, d119342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20208 q ha hb
  have h3 (q : Pattern) (ha : d21755 q = 1) (hb : d119177 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21755, d119177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20208 q ha hb
    | true =>
      simp only [d21755, d119177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d22065 q = 1) (hb : d119343 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22065, d119343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22065, d119343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21756 q = 1) (hb : d119178 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21756, d119178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21756, d119178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d22066 q = 1) (hb : d119344 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22066, d119344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22066, d119344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22067 q = 1) (hb : d119345 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22067, d119345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22067, d119345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d119362 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d22096 q = 1) (hb : d119363 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22096, d119363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22096, d119363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d119363 q = 1) (hb : d120771 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d120771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro20248 (p : Pattern) (ha : d119373 p = 1) (hb : d120777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119347 q = 1) (hb : d120767 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119347, d120767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20245 q ha hb
    | true =>
      simp only [d119347, d120767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20246 q ha hb
  have h2 (q : Pattern) (ha : d119348 q = 1) (hb : d120768 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119348, d120768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119348, d120768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119349 q = 1) (hb : d120769 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119349, d120769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119349, d120769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d119357 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d119358 q = 1) (hb : d120770 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119358, d120770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119358, d120770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d119364 q = 1) (hb : d120772 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119364, d120772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20246 q ha hb
    | true =>
      simp only [d119364, d120772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20247 q ha hb
  have h7 (q : Pattern) (ha : d119365 q = 1) (hb : d120773 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119365, d120773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119365, d120773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119366 q = 1) (hb : d120774 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119366, d120774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119366, d120774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d119370 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d119371 q = 1) (hb : d120775 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119371, d120775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d119371, d120775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d119372 q = 1) (hb : d120776 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d119372, d120776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119372, d120776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d119373 q = 1) (hb : d120777 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d119373, d120777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d119373, d120777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro20249 (p : Pattern) (ha : d119378 p = 1) (hb : d120781 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119364 q = 1) (hb : d120772 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119364, d120772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20246 q ha hb
    | true =>
      simp only [d119364, d120772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20247 q ha hb
  have h2 (q : Pattern) (ha : d119365 q = 1) (hb : d120773 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119365, d120773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119365, d120773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119366 q = 1) (hb : d120774 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119366, d120774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119366, d120774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d119370 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d119371 q = 1) (hb : d120775 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119371, d120775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119371, d120775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d119376 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d119377 q = 1) (hb : d120780 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d119377, d120780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119377, d120780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d119378 q = 1) (hb : d120781 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d119378, d120781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119378, d120781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
end NetHack.Soko22Hazard87
