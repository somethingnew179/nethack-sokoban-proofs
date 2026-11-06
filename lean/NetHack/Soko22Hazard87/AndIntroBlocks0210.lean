import NetHack.Soko22Hazard87.AndIntroBlocks0209
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro52500 (p : Pattern) (ha : d16965 p = 1) (hb : d162092 p = 1) : d162831 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16935 q = 1) (hb : d162092 q = 1) : d162729 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16935, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52491 q ha hb
    | true =>
      simp only [d16935, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16936 q = 1) (hb : d162092 q = 1) : d162730 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16936, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16936, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16937 q = 1) (hb : d162092 q = 1) : d162806 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16937, d162806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16937, d162806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16938 q = 1) (hb : d162092 q = 1) : d162807 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16938, d162807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16938, d162807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16939 q = 1) (hb : d162092 q = 1) : d162808 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16939, d162808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16939, d162808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16965 q = 1) (hb : d162092 q = 1) : d162831 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16965, d162831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16965, d162831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52501 (p : Pattern) (ha : d128362 p = 1) (hb : d162092 p = 1) : d162837 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16846 q = 1) (hb : d162092 q = 1) : d162766 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16846, d162766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52483 q ha hb
    | true =>
      simp only [d16846, d162766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52484 q ha hb
  have h2 (q : Pattern) (ha : d16847 q = 1) (hb : d162092 q = 1) : d162767 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16847, d162767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16847, d162767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16848 q = 1) (hb : d162092 q = 1) : d162768 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16848, d162768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16848, d162768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16849 q = 1) (hb : d162092 q = 1) : d162769 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16849, d162769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16849, d162769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16856 q = 1) (hb : d162092 q = 1) : d162776 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16856, d162776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52485 q ha hb
    | true =>
      simp only [d16856, d162776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52486 q ha hb
  have h6 (q : Pattern) (ha : d16857 q = 1) (hb : d162092 q = 1) : d162777 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16857, d162777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16857, d162777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16858 q = 1) (hb : d162092 q = 1) : d162778 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16858, d162778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16858, d162778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16890 q = 1) (hb : d162092 q = 1) : d162804 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16890, d162804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52490 q ha hb
    | true =>
      simp only [d16890, d162804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52474 q ha hb
  have h9 (q : Pattern) (ha : d128353 q = 1) (hb : d162092 q = 1) : d162805 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128353, d162805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128353, d162805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16941 q = 1) (hb : d162092 q = 1) : d162810 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16941, d162810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52492 q ha hb
    | true =>
      simp only [d16941, d162810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16942 q = 1) (hb : d162092 q = 1) : d162811 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16942, d162811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16942, d162811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128354 q = 1) (hb : d162092 q = 1) : d162812 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128354, d162812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128354, d162812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128355 q = 1) (hb : d162092 q = 1) : d162813 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128355, d162813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128355, d162813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128356 q = 1) (hb : d162092 q = 1) : d162814 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128356, d162814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128356, d162814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16949 q = 1) (hb : d162092 q = 1) : d162818 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16949, d162818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52494 q ha hb
    | true =>
      simp only [d16949, d162818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52495 q ha hb
  have h16 (q : Pattern) (ha : d16950 q = 1) (hb : d162092 q = 1) : d162819 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16950, d162819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16950, d162819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16951 q = 1) (hb : d162092 q = 1) : d162820 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16951, d162820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16951, d162820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16952 q = 1) (hb : d162092 q = 1) : d162821 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16952, d162821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16952, d162821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16955 q = 1) (hb : d162092 q = 1) : d162824 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16955, d162824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52496 q ha hb
    | true =>
      simp only [d16955, d162824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52497 q ha hb
  have h20 (q : Pattern) (ha : d16956 q = 1) (hb : d162092 q = 1) : d162825 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16956, d162825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16956, d162825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d16957 q = 1) (hb : d162092 q = 1) : d162826 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16957, d162826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d16957, d162826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d16960 q = 1) (hb : d162092 q = 1) : d162829 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16960, d162829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52498 q ha hb
    | true =>
      simp only [d16960, d162829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52499 q ha hb
  have h23 (q : Pattern) (ha : d128358 q = 1) (hb : d162092 q = 1) : d162830 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128358, d162830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128358, d162830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d16966 q = 1) (hb : d162092 q = 1) : d162832 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16966, d162832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52500 q ha hb
    | true =>
      simp only [d16966, d162832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d16967 q = 1) (hb : d162092 q = 1) : d162833 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16967, d162833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d16967, d162833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d128359 q = 1) (hb : d162092 q = 1) : d162834 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128359, d162834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d128359, d162834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d128360 q = 1) (hb : d162092 q = 1) : d162835 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128360, d162835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128360, d162835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d128361 q = 1) (hb : d162092 q = 1) : d162836 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128361, d162836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128361, d162836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d128362 q = 1) (hb : d162092 q = 1) : d162837 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128362, d162837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128362, d162837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro52502 (p : Pattern) (ha : d128369 p = 1) (hb : d162092 p = 1) : d162862 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16960 q = 1) (hb : d162092 q = 1) : d162829 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16960, d162829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52498 q ha hb
    | true =>
      simp only [d16960, d162829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52499 q ha hb
  have h2 (q : Pattern) (ha : d128358 q = 1) (hb : d162092 q = 1) : d162830 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128358, d162830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128358, d162830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16966 q = 1) (hb : d162092 q = 1) : d162832 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16966, d162832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52500 q ha hb
    | true =>
      simp only [d16966, d162832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16967 q = 1) (hb : d162092 q = 1) : d162833 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16967, d162833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16967, d162833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128359 q = 1) (hb : d162092 q = 1) : d162834 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128359, d162834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128359, d162834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128367 q = 1) (hb : d162092 q = 1) : d162860 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128367, d162860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128367, d162860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128368 q = 1) (hb : d162092 q = 1) : d162861 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128368, d162861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128368, d162861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128369 q = 1) (hb : d162092 q = 1) : d162862 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128369, d162862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128369, d162862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52503 (p : Pattern) (ha : d15417 p = 1) (hb : d162092 p = 1) : d6501 p = 1 := by
  have h0 (q : Pattern) (ha : d6500 q = 1) (hb : d162091 q = 1) : d6500 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15416 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15417 q = 1) (hb : d162092 q = 1) : d6501 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15417, d162092, d6501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15417, d162092, d6501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro52504 (p : Pattern) (ha : d17010 p = 1) (hb : d162092 p = 1) : d162870 p = 1 := by
  have h0 (q : Pattern) (ha : d17008 q = 1) (hb : d162091 q = 1) : d17008 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17009 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17010 q = 1) (hb : d162092 q = 1) : d162870 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17010, d162092, d162870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17010, d162092, d162870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro52505 (p : Pattern) (ha : d17017 p = 1) (hb : d162092 p = 1) : d162872 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1860 q = 1) : d1860 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17011 q = 1) (hb : d116750 q = 1) : d22508 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17011, d22508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17011, d22508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51744 q ha hb
  have h3 (q : Pattern) (ha : d10074 q = 1) (hb : d116750 q = 1) : d22220 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10074, d22220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51744 q ha hb
    | true =>
      simp only [d10074, d22220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d17012 q = 1) (hb : d116750 q = 1) : d22509 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17012, d22509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17012, d22509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10076 q = 1) (hb : d116750 q = 1) : d22221 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10076, d22221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10076, d22221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d17013 q = 1) (hb : d116750 q = 1) : d22510 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17013, d22510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17013, d22510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17014 q = 1) (hb : d116750 q = 1) : d22511 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17014, d22511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17014, d22511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d17015 q = 1) (hb : d162091 q = 1) : d162871 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17015, d162091, d162871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d17015, d162091, d162871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d17016 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17017 q = 1) (hb : d162092 q = 1) : d162872 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17017, d162092, d162872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17017, d162092, d162872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro52506 (p : Pattern) (ha : d17022 p = 1) (hb : d162092 p = 1) : d13495 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d13489 q = 1) : d13489 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15397 q = 1) (hb : d116750 q = 1) : d13490 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15397, d13490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15397, d13490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36999 q ha hb
  have h3 (q : Pattern) (ha : d10085 q = 1) (hb : d116750 q = 1) : d13351 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d13351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36999 q ha hb
    | true =>
      simp only [d10085, d13351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d15398 q = 1) (hb : d116750 q = 1) : d13491 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15398, d13491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15398, d13491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10087 q = 1) (hb : d116750 q = 1) : d13352 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d13352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10087, d13352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d15399 q = 1) (hb : d116750 q = 1) : d13492 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15399, d13492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15399, d13492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15400 q = 1) (hb : d116750 q = 1) : d13493 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15400, d13493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15400, d13493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d17021 q = 1) (hb : d162091 q = 1) : d13494 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17021, d162091, d13494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d17021, d162091, d13494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d15401 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17022 q = 1) (hb : d162092 q = 1) : d13495 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17022, d162092, d13495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17022, d162092, d13495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro52507 (p : Pattern) (ha : d17041 p = 1) (hb : d162092 p = 1) : d162890 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17018 q = 1) (hb : d162092 q = 1) : d162873 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17018, d162873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52504 q ha hb
    | true =>
      simp only [d17018, d162873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52505 q ha hb
  have h2 (q : Pattern) (ha : d17019 q = 1) (hb : d162092 q = 1) : d162874 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17019, d162874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17019, d162874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17020 q = 1) (hb : d162092 q = 1) : d162875 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17020, d162875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17020, d162875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17023 q = 1) (hb : d162092 q = 1) : d162876 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17023, d162876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52505 q ha hb
    | true =>
      simp only [d17023, d162876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52506 q ha hb
  have h5 (q : Pattern) (ha : d17024 q = 1) (hb : d162092 q = 1) : d162877 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17024, d162877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17024, d162877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17025 q = 1) (hb : d162092 q = 1) : d162878 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17025, d162878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17025, d162878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17026 q = 1) (hb : d162092 q = 1) : d162879 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17026, d162879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17026, d162879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17033 q = 1) (hb : d162092 q = 1) : d162882 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d162882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52505 q ha hb
    | true =>
      simp only [d17033, d162882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52479 q ha hb
  have h9 (q : Pattern) (ha : d17034 q = 1) (hb : d162092 q = 1) : d162883 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d162883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17034, d162883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17035 q = 1) (hb : d162092 q = 1) : d162884 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d162884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, d162884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17036 q = 1) (hb : d162092 q = 1) : d162885 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d162885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52479 q ha hb
    | true =>
      simp only [d17036, d162885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52503 q ha hb
  have h12 (q : Pattern) (ha : d17037 q = 1) (hb : d162092 q = 1) : d162886 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d162886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17037, d162886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17038 q = 1) (hb : d162092 q = 1) : d162887 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d162887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, d162887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17039 q = 1) (hb : d162092 q = 1) : d162888 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d162888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17039, d162888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17040 q = 1) (hb : d162092 q = 1) : d162889 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17040, d162889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17040, d162889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17041 q = 1) (hb : d162092 q = 1) : d162890 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17041, d162890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d17041, d162890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro52508 (p : Pattern) (ha : d17046 p = 1) (hb : d162092 p = 1) : d162895 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17033 q = 1) (hb : d162092 q = 1) : d162882 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d162882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52505 q ha hb
    | true =>
      simp only [d17033, d162882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52479 q ha hb
  have h2 (q : Pattern) (ha : d17034 q = 1) (hb : d162092 q = 1) : d162883 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d162883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17034, d162883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17035 q = 1) (hb : d162092 q = 1) : d162884 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d162884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, d162884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17036 q = 1) (hb : d162092 q = 1) : d162885 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d162885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52479 q ha hb
    | true =>
      simp only [d17036, d162885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52503 q ha hb
  have h5 (q : Pattern) (ha : d17037 q = 1) (hb : d162092 q = 1) : d162886 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d162886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17037, d162886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17038 q = 1) (hb : d162092 q = 1) : d162887 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d162887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, d162887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17039 q = 1) (hb : d162092 q = 1) : d162888 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d162888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17039, d162888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17044 q = 1) (hb : d162092 q = 1) : d162893 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17044, d162893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17044, d162893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17045 q = 1) (hb : d162092 q = 1) : d162894 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17045, d162894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17045, d162894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17046 q = 1) (hb : d162092 q = 1) : d162895 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17046, d162895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17046, d162895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro52509 (p : Pattern) (ha : d17052 p = 1) (hb : d162092 p = 1) : d162901 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17042 q = 1) (hb : d162092 q = 1) : d162891 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17042, d162891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52507 q ha hb
    | true =>
      simp only [d17042, d162891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17043 q = 1) (hb : d162092 q = 1) : d162892 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17043, d162892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17043, d162892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17047 q = 1) (hb : d162092 q = 1) : d162896 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17047, d162896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52508 q ha hb
    | true =>
      simp only [d17047, d162896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17048 q = 1) (hb : d162092 q = 1) : d162897 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17048, d162897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17048, d162897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17049 q = 1) (hb : d162092 q = 1) : d162898 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17049, d162898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17049, d162898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17050 q = 1) (hb : d162092 q = 1) : d162899 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17050, d162899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17050, d162899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17051 q = 1) (hb : d162092 q = 1) : d162900 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17051, d162900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17051, d162900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17052 q = 1) (hb : d162092 q = 1) : d162901 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17052, d162901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17052, d162901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro52510 (p : Pattern) (ha : d17064 p = 1) (hb : d162092 p = 1) : d162913 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17047 q = 1) (hb : d162092 q = 1) : d162896 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17047, d162896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52508 q ha hb
    | true =>
      simp only [d17047, d162896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17048 q = 1) (hb : d162092 q = 1) : d162897 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17048, d162897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17048, d162897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17059 q = 1) (hb : d162092 q = 1) : d162908 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17059, d162908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52480 q ha hb
    | true =>
      simp only [d17059, d162908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17060 q = 1) (hb : d162092 q = 1) : d162909 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17060, d162909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17060, d162909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17061 q = 1) (hb : d162092 q = 1) : d162910 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17061, d162910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17061, d162910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17062 q = 1) (hb : d162092 q = 1) : d162911 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17062, d162911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17062, d162911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17063 q = 1) (hb : d162092 q = 1) : d162912 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17063, d162912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17063, d162912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17064 q = 1) (hb : d162092 q = 1) : d162913 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17064, d162913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17064, d162913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro52511 (p : Pattern) (ha : d17113 p = 1) (hb : d162092 p = 1) : d162917 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17033 q = 1) (hb : d162092 q = 1) : d162882 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d162882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52505 q ha hb
    | true =>
      simp only [d17033, d162882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52479 q ha hb
  have h2 (q : Pattern) (ha : d17034 q = 1) (hb : d162092 q = 1) : d162883 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d162883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17034, d162883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17035 q = 1) (hb : d162092 q = 1) : d162884 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d162884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, d162884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17036 q = 1) (hb : d162092 q = 1) : d162885 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d162885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52479 q ha hb
    | true =>
      simp only [d17036, d162885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52503 q ha hb
  have h5 (q : Pattern) (ha : d17037 q = 1) (hb : d162092 q = 1) : d162886 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d162886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17037, d162886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17038 q = 1) (hb : d162092 q = 1) : d162887 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d162887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, d162887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17039 q = 1) (hb : d162092 q = 1) : d162888 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d162888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17039, d162888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13516 q = 1) (hb : d162092 q = 1) : d13516 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d17108 q = 1) (hb : d162092 q = 1) : d162902 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17108, d162902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52479 q ha hb
    | true =>
      simp only [d17108, d162902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17109 q = 1) (hb : d162092 q = 1) : d162903 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17109, d162903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17109, d162903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17110 q = 1) (hb : d162092 q = 1) : d162904 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17110, d162904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17110, d162904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17111 q = 1) (hb : d162092 q = 1) : d162905 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17111, d162905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17111, d162905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d17112 q = 1) (hb : d162092 q = 1) : d162916 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17112, d162916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17112, d162916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17113 q = 1) (hb : d162092 q = 1) : d162917 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17113, d162917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d17113, d162917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro52512 (p : Pattern) (ha : d17119 p = 1) (hb : d162092 p = 1) : d162923 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17114 q = 1) (hb : d162092 q = 1) : d162918 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17114, d162918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52511 q ha hb
    | true =>
      simp only [d17114, d162918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17115 q = 1) (hb : d162092 q = 1) : d162919 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17115, d162919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17115, d162919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17116 q = 1) (hb : d162092 q = 1) : d162920 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17116, d162920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17116, d162920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17117 q = 1) (hb : d162092 q = 1) : d162921 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17117, d162921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17117, d162921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17118 q = 1) (hb : d162092 q = 1) : d162922 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17118, d162922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17118, d162922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17119 q = 1) (hb : d162092 q = 1) : d162923 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17119, d162923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17119, d162923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52513 (p : Pattern) (ha : d128379 p = 1) (hb : d162092 p = 1) : d162929 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17065 q = 1) (hb : d162092 q = 1) : d162914 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17065, d162914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52509 q ha hb
    | true =>
      simp only [d17065, d162914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52510 q ha hb
  have h2 (q : Pattern) (ha : d128375 q = 1) (hb : d162092 q = 1) : d162915 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128375, d162915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128375, d162915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17120 q = 1) (hb : d162092 q = 1) : d162924 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17120, d162924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52512 q ha hb
    | true =>
      simp only [d17120, d162924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17121 q = 1) (hb : d162092 q = 1) : d162925 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17121, d162925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17121, d162925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128376 q = 1) (hb : d162092 q = 1) : d162926 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128376, d162926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128376, d162926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128377 q = 1) (hb : d162092 q = 1) : d162927 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128377, d162927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128377, d162927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128378 q = 1) (hb : d162092 q = 1) : d162928 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128378, d162928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128378, d162928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128379 q = 1) (hb : d162092 q = 1) : d162929 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128379, d162929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128379, d162929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52514 (p : Pattern) (ha : d128385 p = 1) (hb : d162092 p = 1) : d162946 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16829 q = 1) (hb : d162092 q = 1) : d162749 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16829, d162749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16829, d162749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52469 q ha hb
  have h2 (q : Pattern) (ha : d16830 q = 1) (hb : d162092 q = 1) : d162750 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16830, d162750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16830, d162750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16839 q = 1) (hb : d162092 q = 1) : d162759 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16839, d162759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52469 q ha hb
    | true =>
      simp only [d16839, d162759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52472 q ha hb
  have h4 (q : Pattern) (ha : d16840 q = 1) (hb : d162092 q = 1) : d162760 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16840, d162760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16840, d162760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16841 q = 1) (hb : d162092 q = 1) : d162761 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d16841, d162761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16841, d162761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128363 q = 1) (hb : d162092 q = 1) : d162838 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128363, d162838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52493 q ha hb
    | true =>
      simp only [d128363, d162838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52501 q ha hb
  have h7 (q : Pattern) (ha : d16990 q = 1) (hb : d162092 q = 1) : d162856 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16990, d162856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52475 q ha hb
    | true =>
      simp only [d16990, d162856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52476 q ha hb
  have h8 (q : Pattern) (ha : d128364 q = 1) (hb : d162092 q = 1) : d162857 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128364, d162857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128364, d162857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128365 q = 1) (hb : d162092 q = 1) : d162858 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128365, d162858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128365, d162858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d128366 q = 1) (hb : d162092 q = 1) : d162859 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128366, d162859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128366, d162859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128370 q = 1) (hb : d162092 q = 1) : d162863 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128370, d162863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128370, d162863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52502 q ha hb
  have h12 (q : Pattern) (ha : d16999 q = 1) (hb : d162092 q = 1) : d162865 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16999, d162865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16999, d162865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52477 q ha hb
  have h13 (q : Pattern) (ha : d128371 q = 1) (hb : d162092 q = 1) : d162866 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128371, d162866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128371, d162866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128372 q = 1) (hb : d162092 q = 1) : d162867 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128372, d162867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128372, d162867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d128373 q = 1) (hb : d162092 q = 1) : d162868 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128373, d162868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128373, d162868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d128374 q = 1) (hb : d162092 q = 1) : d162869 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128374, d162869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128374, d162869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128380 q = 1) (hb : d162092 q = 1) : d162930 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128380, d162930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128380, d162930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52513 q ha hb
  have h18 (q : Pattern) (ha : d17137 q = 1) (hb : d162092 q = 1) : d162941 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17137, d162941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17137, d162941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52482 q ha hb
  have h19 (q : Pattern) (ha : d128381 q = 1) (hb : d162092 q = 1) : d162942 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128381, d162942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128381, d162942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d128382 q = 1) (hb : d162092 q = 1) : d162943 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128382, d162943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d128382, d162943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d128383 q = 1) (hb : d162092 q = 1) : d162944 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128383, d162944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128383, d162944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d128384 q = 1) (hb : d162092 q = 1) : d162945 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128384, d162945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128384, d162945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d128385 q = 1) (hb : d162092 q = 1) : d162946 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128385, d162946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128385, d162946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro52515 (p : Pattern) (ha : d128391 p = 1) (hb : d162092 p = 1) : d162952 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128386 q = 1) (hb : d162092 q = 1) : d162947 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128386, d162947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128386, d162947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52514 q ha hb
  have h2 (q : Pattern) (ha : d128387 q = 1) (hb : d162092 q = 1) : d162948 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128387, d162948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128387, d162948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128388 q = 1) (hb : d162092 q = 1) : d162949 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128388, d162949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128388, d162949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128389 q = 1) (hb : d162092 q = 1) : d162950 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128389, d162950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128389, d162950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128390 q = 1) (hb : d162092 q = 1) : d162951 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128390, d162951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128390, d162951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128391 q = 1) (hb : d162092 q = 1) : d162952 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128391, d162952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128391, d162952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52516 (p : Pattern) (ha : d15558 p = 1) (hb : d162092 p = 1) : d5252 p = 1 := by
  have h0 (q : Pattern) (ha : d5251 q = 1) (hb : d162091 q = 1) : d5251 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15557 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15558 q = 1) (hb : d162092 q = 1) : d5252 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15558, d162092, d5252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15558, d162092, d5252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro52517 (p : Pattern) (ha : d15563 p = 1) (hb : d162092 p = 1) : d13614 p = 1 := by
  have h0 (q : Pattern) (ha : d2071 q = 1) (hb : d162091 q = 1) : d2071 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15557 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15563 q = 1) (hb : d162092 q = 1) : d13614 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15563, d162092, d13614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15563, d162092, d13614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro52518 (p : Pattern) (ha : d17157 p = 1) (hb : d162092 p = 1) : d162957 p = 1 := by
  have h0 (q : Pattern) (ha : d17155 q = 1) (hb : d162091 q = 1) : d17155 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17156 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17157 q = 1) (hb : d162092 q = 1) : d162957 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17157, d162092, d162957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17157, d162092, d162957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro52519 (p : Pattern) (ha : d17161 p = 1) (hb : d162092 p = 1) : d162959 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2056 q = 1) : d2056 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10391 q = 1) (hb : d116750 q = 1) : d22688 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10391, d22688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51804 q ha hb
    | true =>
      simp only [d10391, d22688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10393 q = 1) (hb : d116750 q = 1) : d22689 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10393, d22689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10393, d22689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d17158 q = 1) (hb : d116750 q = 1) : d22690 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17158, d22690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17158, d22690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17159 q = 1) (hb : d116750 q = 1) : d22691 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17159, d22691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17159, d22691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d17160 q = 1) (hb : d162091 q = 1) : d162958 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17160, d162091, d162958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d17160, d162091, d162958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d15550 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d17161 q = 1) (hb : d162092 q = 1) : d162959 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17161, d162092, d162959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17161, d162092, d162959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro52520 (p : Pattern) (ha : d17174 p = 1) (hb : d162092 p = 1) : d162972 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17162 q = 1) (hb : d162092 q = 1) : d162960 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, d162960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52518 q ha hb
    | true =>
      simp only [d17162, d162960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52519 q ha hb
  have h2 (q : Pattern) (ha : d17163 q = 1) (hb : d162092 q = 1) : d162961 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17163, d162961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17163, d162961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17164 q = 1) (hb : d162092 q = 1) : d162962 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17164, d162962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17164, d162962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17165 q = 1) (hb : d162092 q = 1) : d162963 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, d162963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52519 q ha hb
    | true =>
      simp only [d17165, d162963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52516 q ha hb
  have h5 (q : Pattern) (ha : d17166 q = 1) (hb : d162092 q = 1) : d162964 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17166, d162964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17166, d162964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17167 q = 1) (hb : d162092 q = 1) : d162965 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17167, d162965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17167, d162965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17168 q = 1) (hb : d162092 q = 1) : d162966 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17168, d162966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17168, d162966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17169 q = 1) (hb : d162092 q = 1) : d162967 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17169, d162967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52519 q ha hb
    | true =>
      simp only [d17169, d162967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52517 q ha hb
  have h9 (q : Pattern) (ha : d17170 q = 1) (hb : d162092 q = 1) : d162968 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17170, d162968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17170, d162968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17171 q = 1) (hb : d162092 q = 1) : d162969 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17171, d162969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17171, d162969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17172 q = 1) (hb : d162092 q = 1) : d162970 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17172, d162970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17172, d162970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d17173 q = 1) (hb : d162092 q = 1) : d162971 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17173, d162971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17173, d162971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17174 q = 1) (hb : d162092 q = 1) : d162972 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17174, d162972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17174, d162972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro52521 (p : Pattern) (ha : d17178 p = 1) (hb : d162092 p = 1) : d162976 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17169 q = 1) (hb : d162092 q = 1) : d162967 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17169, d162967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52519 q ha hb
    | true =>
      simp only [d17169, d162967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52517 q ha hb
  have h2 (q : Pattern) (ha : d17170 q = 1) (hb : d162092 q = 1) : d162968 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17170, d162968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17170, d162968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17171 q = 1) (hb : d162092 q = 1) : d162969 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17171, d162969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17171, d162969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17172 q = 1) (hb : d162092 q = 1) : d162970 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17172, d162970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17172, d162970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17177 q = 1) (hb : d162092 q = 1) : d162975 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17177, d162975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17177, d162975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17178 q = 1) (hb : d162092 q = 1) : d162976 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17178, d162976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17178, d162976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52522 (p : Pattern) (ha : d17184 p = 1) (hb : d162092 p = 1) : d162982 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17175 q = 1) (hb : d162092 q = 1) : d162973 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17175, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52520 q ha hb
    | true =>
      simp only [d17175, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17176 q = 1) (hb : d162092 q = 1) : d162974 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17176, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17176, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d162092 q = 1) : d162977 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52521 q ha hb
    | true =>
      simp only [d17179, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d162092 q = 1) : d162978 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17181 q = 1) (hb : d162092 q = 1) : d162979 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17181, d162979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17181, d162979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17182 q = 1) (hb : d162092 q = 1) : d162980 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17182, d162980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17182, d162980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17183 q = 1) (hb : d162092 q = 1) : d162981 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17183, d162981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17183, d162981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17184 q = 1) (hb : d162092 q = 1) : d162982 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17184, d162982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17184, d162982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52523 (p : Pattern) (ha : d17188 p = 1) (hb : d162092 p = 1) : d162986 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17179 q = 1) (hb : d162092 q = 1) : d162977 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52521 q ha hb
    | true =>
      simp only [d17179, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17180 q = 1) (hb : d162092 q = 1) : d162978 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17185 q = 1) (hb : d162092 q = 1) : d162983 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17185, d162983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17185, d162983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17186 q = 1) (hb : d162092 q = 1) : d162984 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17186, d162984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17186, d162984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17187 q = 1) (hb : d162092 q = 1) : d162985 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17187, d162985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17187, d162985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17188 q = 1) (hb : d162092 q = 1) : d162986 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17188, d162986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17188, d162986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52524 (p : Pattern) (ha : d17194 p = 1) (hb : d162092 p = 1) : d162992 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17189 q = 1) (hb : d162092 q = 1) : d162987 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17189, d162987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52522 q ha hb
    | true =>
      simp only [d17189, d162987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52523 q ha hb
  have h2 (q : Pattern) (ha : d17190 q = 1) (hb : d162092 q = 1) : d162988 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17190, d162988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17190, d162988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17191 q = 1) (hb : d162092 q = 1) : d162989 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17191, d162989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17191, d162989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17192 q = 1) (hb : d162092 q = 1) : d162990 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17192, d162990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17192, d162990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17193 q = 1) (hb : d162092 q = 1) : d162991 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17193, d162991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17193, d162991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17194 q = 1) (hb : d162092 q = 1) : d162992 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17194, d162992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17194, d162992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52525 (p : Pattern) (ha : d17197 p = 1) (hb : d162092 p = 1) : d162995 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17175 q = 1) (hb : d162092 q = 1) : d162973 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17175, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52520 q ha hb
    | true =>
      simp only [d17175, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17176 q = 1) (hb : d162092 q = 1) : d162974 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17176, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17176, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d162092 q = 1) : d162977 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52521 q ha hb
    | true =>
      simp only [d17179, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d162092 q = 1) : d162978 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17181 q = 1) (hb : d162092 q = 1) : d162979 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17181, d162979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17181, d162979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17182 q = 1) (hb : d162092 q = 1) : d162980 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17182, d162980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17182, d162980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17183 q = 1) (hb : d162092 q = 1) : d162981 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17183, d162981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17183, d162981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17197 q = 1) (hb : d162092 q = 1) : d162995 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17197, d162995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17197, d162995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro52526 (p : Pattern) (ha : d17198 p = 1) (hb : d162092 p = 1) : d162996 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17179 q = 1) (hb : d162092 q = 1) : d162977 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52521 q ha hb
    | true =>
      simp only [d17179, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17180 q = 1) (hb : d162092 q = 1) : d162978 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17185 q = 1) (hb : d162092 q = 1) : d162983 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17185, d162983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17185, d162983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17186 q = 1) (hb : d162092 q = 1) : d162984 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17186, d162984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17186, d162984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17187 q = 1) (hb : d162092 q = 1) : d162985 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17187, d162985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17187, d162985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17198 q = 1) (hb : d162092 q = 1) : d162996 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17198, d162996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17198, d162996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52527 (p : Pattern) (ha : d17204 p = 1) (hb : d162092 p = 1) : d163002 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17189 q = 1) (hb : d162092 q = 1) : d162987 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17189, d162987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52522 q ha hb
    | true =>
      simp only [d17189, d162987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52523 q ha hb
  have h2 (q : Pattern) (ha : d17190 q = 1) (hb : d162092 q = 1) : d162988 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17190, d162988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17190, d162988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17191 q = 1) (hb : d162092 q = 1) : d162989 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17191, d162989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17191, d162989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17192 q = 1) (hb : d162092 q = 1) : d162990 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17192, d162990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17192, d162990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17193 q = 1) (hb : d162092 q = 1) : d162991 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17193, d162991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17193, d162991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17199 q = 1) (hb : d162092 q = 1) : d162997 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17199, d162997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52525 q ha hb
    | true =>
      simp only [d17199, d162997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52526 q ha hb
  have h7 (q : Pattern) (ha : d17200 q = 1) (hb : d162092 q = 1) : d162998 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17200, d162998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17200, d162998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17201 q = 1) (hb : d162092 q = 1) : d162999 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17201, d162999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17201, d162999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17202 q = 1) (hb : d162092 q = 1) : d163000 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17202, d163000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17202, d163000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17203 q = 1) (hb : d162092 q = 1) : d163001 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17203, d163001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17203, d163001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17204 q = 1) (hb : d162092 q = 1) : d163002 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17204, d163002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17204, d163002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro52528 (p : Pattern) (ha : d17244 p = 1) (hb : d162092 p = 1) : d163037 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17162 q = 1) (hb : d162092 q = 1) : d162960 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, d162960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52518 q ha hb
    | true =>
      simp only [d17162, d162960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52519 q ha hb
  have h2 (q : Pattern) (ha : d17163 q = 1) (hb : d162092 q = 1) : d162961 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17163, d162961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17163, d162961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17164 q = 1) (hb : d162092 q = 1) : d162962 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17164, d162962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17164, d162962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17165 q = 1) (hb : d162092 q = 1) : d162963 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, d162963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52519 q ha hb
    | true =>
      simp only [d17165, d162963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52516 q ha hb
  have h5 (q : Pattern) (ha : d17166 q = 1) (hb : d162092 q = 1) : d162964 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17166, d162964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17166, d162964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17167 q = 1) (hb : d162092 q = 1) : d162965 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17167, d162965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17167, d162965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17168 q = 1) (hb : d162092 q = 1) : d162966 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17168, d162966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17168, d162966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17242 q = 1) (hb : d162092 q = 1) : d163035 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17242, d163035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17242, d163035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17243 q = 1) (hb : d162092 q = 1) : d163036 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17243, d163036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17243, d163036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17244 q = 1) (hb : d162092 q = 1) : d163037 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17244, d163037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17244, d163037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro52529 (p : Pattern) (ha : d17254 p = 1) (hb : d162092 p = 1) : d163047 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17245 q = 1) (hb : d162092 q = 1) : d163038 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17245, d163038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52528 q ha hb
    | true =>
      simp only [d17245, d163038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17246 q = 1) (hb : d162092 q = 1) : d163039 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17246, d163039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17246, d163039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d162092 q = 1) : d162977 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52521 q ha hb
    | true =>
      simp only [d17179, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d162092 q = 1) : d162978 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17251 q = 1) (hb : d162092 q = 1) : d163044 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17251, d163044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17251, d163044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17252 q = 1) (hb : d162092 q = 1) : d163045 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17252, d163045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17252, d163045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17253 q = 1) (hb : d162092 q = 1) : d163046 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17253, d163046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17253, d163046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17254 q = 1) (hb : d162092 q = 1) : d163047 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17254, d163047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17254, d163047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52530 (p : Pattern) (ha : d17348 p = 1) (hb : d162092 p = 1) : d163093 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17338 q = 1) (hb : d162092 q = 1) : d163083 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17338, d163083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52529 q ha hb
    | true =>
      simp only [d17338, d163083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52523 q ha hb
  have h2 (q : Pattern) (ha : d17339 q = 1) (hb : d162092 q = 1) : d163084 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17339, d163084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17339, d163084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17340 q = 1) (hb : d162092 q = 1) : d163085 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17340, d163085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17340, d163085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17341 q = 1) (hb : d162092 q = 1) : d163086 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17341, d163086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17341, d163086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17342 q = 1) (hb : d162092 q = 1) : d163087 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17342, d163087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17342, d163087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17343 q = 1) (hb : d162092 q = 1) : d163088 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17343, d163088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52523 q ha hb
    | true =>
      simp only [d17343, d163088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17344 q = 1) (hb : d162092 q = 1) : d163089 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17344, d163089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17344, d163089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17345 q = 1) (hb : d162092 q = 1) : d163090 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17345, d163090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17345, d163090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17346 q = 1) (hb : d162092 q = 1) : d163091 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17346, d163091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17346, d163091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17347 q = 1) (hb : d162092 q = 1) : d163092 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17347, d163092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17347, d163092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17348 q = 1) (hb : d162092 q = 1) : d163093 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17348, d163093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17348, d163093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro52531 (p : Pattern) (ha : d17354 p = 1) (hb : d162092 p = 1) : d163099 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17343 q = 1) (hb : d162092 q = 1) : d163088 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17343, d163088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52523 q ha hb
    | true =>
      simp only [d17343, d163088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17344 q = 1) (hb : d162092 q = 1) : d163089 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17344, d163089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17344, d163089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17345 q = 1) (hb : d162092 q = 1) : d163090 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17345, d163090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17345, d163090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17346 q = 1) (hb : d162092 q = 1) : d163091 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17346, d163091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17346, d163091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17347 q = 1) (hb : d162092 q = 1) : d163092 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17347, d163092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17347, d163092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17349 q = 1) (hb : d162092 q = 1) : d163094 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17349, d163094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52526 q ha hb
    | true =>
      simp only [d17349, d163094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17350 q = 1) (hb : d162092 q = 1) : d163095 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17350, d163095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17350, d163095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17351 q = 1) (hb : d162092 q = 1) : d163096 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17351, d163096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17351, d163096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17352 q = 1) (hb : d162092 q = 1) : d163097 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17352, d163097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17352, d163097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17353 q = 1) (hb : d162092 q = 1) : d163098 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17353, d163098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17353, d163098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17354 q = 1) (hb : d162092 q = 1) : d163099 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17354, d163099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17354, d163099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro52532 (p : Pattern) (ha : d17363 p = 1) (hb : d162092 p = 1) : d163108 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17349 q = 1) (hb : d162092 q = 1) : d163094 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17349, d163094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52526 q ha hb
    | true =>
      simp only [d17349, d163094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17350 q = 1) (hb : d162092 q = 1) : d163095 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17350, d163095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17350, d163095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17351 q = 1) (hb : d162092 q = 1) : d163096 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17351, d163096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17351, d163096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17352 q = 1) (hb : d162092 q = 1) : d163097 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17352, d163097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17352, d163097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17353 q = 1) (hb : d162092 q = 1) : d163098 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17353, d163098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17353, d163098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17363 q = 1) (hb : d162092 q = 1) : d163108 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17363, d163108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17363, d163108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52533 (p : Pattern) (ha : d15813 p = 1) (hb : d162092 p = 1) : d13843 p = 1 := by
  have h0 (q : Pattern) (ha : d2355 q = 1) (hb : d162091 q = 1) : d2355 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15794 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15813 q = 1) (hb : d162092 q = 1) : d13843 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15813, d162092, d13843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15813, d162092, d13843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro52534 (p : Pattern) (ha : d17396 p = 1) (hb : d162092 p = 1) : d163124 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2343 q = 1) : d2343 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17391 q = 1) (hb : d116750 q = 1) : d22943 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17391, d22943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17391, d22943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51804 q ha hb
  have h3 (q : Pattern) (ha : d10391 q = 1) (hb : d116750 q = 1) : d22688 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10391, d22688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51804 q ha hb
    | true =>
      simp only [d10391, d22688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d17392 q = 1) (hb : d116750 q = 1) : d22944 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17392, d22944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17392, d22944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10393 q = 1) (hb : d116750 q = 1) : d22689 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10393, d22689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10393, d22689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d17393 q = 1) (hb : d116750 q = 1) : d22945 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17393, d22945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17393, d22945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17394 q = 1) (hb : d116750 q = 1) : d22946 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17394, d22946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17394, d22946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d17395 q = 1) (hb : d162091 q = 1) : d163123 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17395, d162091, d163123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d17395, d162091, d163123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d15779 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17396 q = 1) (hb : d162092 q = 1) : d163124 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17396, d162092, d163124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17396, d162092, d163124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro52535 (p : Pattern) (ha : d17422 p = 1) (hb : d162092 p = 1) : d163150 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17417 q = 1) (hb : d162092 q = 1) : d163145 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17417, d163145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52534 q ha hb
    | true =>
      simp only [d17417, d163145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52533 q ha hb
  have h2 (q : Pattern) (ha : d17418 q = 1) (hb : d162092 q = 1) : d163146 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17418, d163146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17418, d163146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17419 q = 1) (hb : d162092 q = 1) : d163147 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17419, d163147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17419, d163147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17420 q = 1) (hb : d162092 q = 1) : d163148 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17420, d163148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17420, d163148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17421 q = 1) (hb : d162092 q = 1) : d163149 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17421, d163149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17421, d163149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17422 q = 1) (hb : d162092 q = 1) : d163150 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17422, d163150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17422, d163150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52536 (p : Pattern) (ha : d17494 p = 1) (hb : d162092 p = 1) : d163177 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17423 q = 1) (hb : d162092 q = 1) : d163151 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17423, d163151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52535 q ha hb
    | true =>
      simp only [d17423, d163151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17424 q = 1) (hb : d162092 q = 1) : d163152 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17424, d163152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17424, d163152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17491 q = 1) (hb : d162092 q = 1) : d163174 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17491, d163174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17491, d163174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17492 q = 1) (hb : d162092 q = 1) : d163175 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17492, d163175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17492, d163175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17493 q = 1) (hb : d162092 q = 1) : d163176 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17493, d163176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17493, d163176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17494 q = 1) (hb : d162092 q = 1) : d163177 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17494, d163177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17494, d163177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52537 (p : Pattern) (ha : d17500 p = 1) (hb : d162092 p = 1) : d163183 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17495 q = 1) (hb : d162092 q = 1) : d163178 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17495, d163178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52536 q ha hb
    | true =>
      simp only [d17495, d163178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17496 q = 1) (hb : d162092 q = 1) : d163179 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17496, d163179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17496, d163179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17497 q = 1) (hb : d162092 q = 1) : d163180 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17497, d163180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17497, d163180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17498 q = 1) (hb : d162092 q = 1) : d163181 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17498, d163181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17498, d163181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17499 q = 1) (hb : d162092 q = 1) : d163182 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17499, d163182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17499, d163182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17500 q = 1) (hb : d162092 q = 1) : d163183 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17500, d163183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17500, d163183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52538 (p : Pattern) (ha : d17209 p = 1) (hb : d162092 p = 1) : d163007 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17175 q = 1) (hb : d162092 q = 1) : d162973 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17175, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52520 q ha hb
    | true =>
      simp only [d17175, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17176 q = 1) (hb : d162092 q = 1) : d162974 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17176, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17176, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d162092 q = 1) : d162977 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52521 q ha hb
    | true =>
      simp only [d17179, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d162092 q = 1) : d162978 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17181 q = 1) (hb : d162092 q = 1) : d162979 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17181, d162979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17181, d162979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17182 q = 1) (hb : d162092 q = 1) : d162980 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17182, d162980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17182, d162980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17208 q = 1) (hb : d162092 q = 1) : d163006 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17208, d163006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17208, d163006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17209 q = 1) (hb : d162092 q = 1) : d163007 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17209, d163007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17209, d163007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52539 (p : Pattern) (ha : d17211 p = 1) (hb : d162092 p = 1) : d163009 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17179 q = 1) (hb : d162092 q = 1) : d162977 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52521 q ha hb
    | true =>
      simp only [d17179, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17180 q = 1) (hb : d162092 q = 1) : d162978 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17185 q = 1) (hb : d162092 q = 1) : d162983 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17185, d162983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17185, d162983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17186 q = 1) (hb : d162092 q = 1) : d162984 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17186, d162984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17186, d162984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17210 q = 1) (hb : d162092 q = 1) : d163008 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17210, d163008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17210, d163008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17211 q = 1) (hb : d162092 q = 1) : d163009 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17211, d163009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17211, d163009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52540 (p : Pattern) (ha : d17218 p = 1) (hb : d162092 p = 1) : d163016 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17175 q = 1) (hb : d162092 q = 1) : d162973 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17175, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52520 q ha hb
    | true =>
      simp only [d17175, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17176 q = 1) (hb : d162092 q = 1) : d162974 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17176, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17176, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d162092 q = 1) : d162977 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52521 q ha hb
    | true =>
      simp only [d17179, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d162092 q = 1) : d162978 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17181 q = 1) (hb : d162092 q = 1) : d162979 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17181, d162979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17181, d162979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17216 q = 1) (hb : d162092 q = 1) : d163014 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17216, d163014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17216, d163014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17217 q = 1) (hb : d162092 q = 1) : d163015 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17217, d163015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17217, d163015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17218 q = 1) (hb : d162092 q = 1) : d163016 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17218, d163016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17218, d163016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52541 (p : Pattern) (ha : d17221 p = 1) (hb : d162092 p = 1) : d163019 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17179 q = 1) (hb : d162092 q = 1) : d162977 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52521 q ha hb
    | true =>
      simp only [d17179, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17180 q = 1) (hb : d162092 q = 1) : d162978 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17185 q = 1) (hb : d162092 q = 1) : d162983 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17185, d162983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17185, d162983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17219 q = 1) (hb : d162092 q = 1) : d163017 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17219, d163017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17219, d163017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17220 q = 1) (hb : d162092 q = 1) : d163018 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17220, d163018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17220, d163018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17221 q = 1) (hb : d162092 q = 1) : d163019 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17221, d163019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17221, d163019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52542 (p : Pattern) (ha : d17229 p = 1) (hb : d162092 p = 1) : d163023 p = 1 := by
  have h0 (q : Pattern) (ha : d17227 q = 1) (hb : d162091 q = 1) : d17227 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17228 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17229 q = 1) (hb : d162092 q = 1) : d163023 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17229, d162092, d163023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17229, d162092, d163023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro52543 (p : Pattern) (ha : d17233 p = 1) (hb : d162092 p = 1) : d13683 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d13676 q = 1) : d13676 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10371 q = 1) (hb : d116750 q = 1) : d13678 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d13678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37057 q ha hb
    | true =>
      simp only [d10371, d13678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10373 q = 1) (hb : d116750 q = 1) : d13679 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, d13679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10373, d13679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d15548 q = 1) (hb : d116750 q = 1) : d13680 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15548, d13680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15548, d13680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15549 q = 1) (hb : d116750 q = 1) : d13681 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15549, d13681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15549, d13681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d17156 q = 1) (hb : d162091 q = 1) : d13682 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17156, d162091, d13682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d17156, d162091, d13682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d15550 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d17233 q = 1) (hb : d162092 q = 1) : d13683 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17233, d162092, d13683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17233, d162092, d13683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro52544 (p : Pattern) (ha : d17239 p = 1) (hb : d162092 p = 1) : d163032 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17230 q = 1) (hb : d162092 q = 1) : d163024 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17230, d163024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52542 q ha hb
    | true =>
      simp only [d17230, d163024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52518 q ha hb
  have h2 (q : Pattern) (ha : d17231 q = 1) (hb : d162092 q = 1) : d163025 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17231, d163025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17231, d163025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17232 q = 1) (hb : d162092 q = 1) : d163026 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17232, d163026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17232, d163026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17234 q = 1) (hb : d162092 q = 1) : d163027 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17234, d163027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52518 q ha hb
    | true =>
      simp only [d17234, d163027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52543 q ha hb
  have h5 (q : Pattern) (ha : d17235 q = 1) (hb : d162092 q = 1) : d163028 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17235, d163028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17235, d163028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17236 q = 1) (hb : d162092 q = 1) : d163029 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17236, d163029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17236, d163029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17237 q = 1) (hb : d162092 q = 1) : d163030 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17237, d163030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17237, d163030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17162 q = 1) (hb : d162092 q = 1) : d162960 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, d162960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52518 q ha hb
    | true =>
      simp only [d17162, d162960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52519 q ha hb
  have h9 (q : Pattern) (ha : d17163 q = 1) (hb : d162092 q = 1) : d162961 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17163, d162961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17163, d162961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17164 q = 1) (hb : d162092 q = 1) : d162962 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17164, d162962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17164, d162962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17165 q = 1) (hb : d162092 q = 1) : d162963 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, d162963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52519 q ha hb
    | true =>
      simp only [d17165, d162963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52516 q ha hb
  have h12 (q : Pattern) (ha : d17166 q = 1) (hb : d162092 q = 1) : d162964 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17166, d162964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17166, d162964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17167 q = 1) (hb : d162092 q = 1) : d162965 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17167, d162965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17167, d162965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17168 q = 1) (hb : d162092 q = 1) : d162966 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17168, d162966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17168, d162966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17238 q = 1) (hb : d162092 q = 1) : d163031 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17238, d163031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17238, d163031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17239 q = 1) (hb : d162092 q = 1) : d163032 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17239, d163032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d17239, d163032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro52545 (p : Pattern) (ha : d17250 p = 1) (hb : d162092 p = 1) : d163043 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17240 q = 1) (hb : d162092 q = 1) : d163033 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17240, d163033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52544 q ha hb
    | true =>
      simp only [d17240, d163033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17241 q = 1) (hb : d162092 q = 1) : d163034 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17241, d163034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17241, d163034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17245 q = 1) (hb : d162092 q = 1) : d163038 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17245, d163038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52528 q ha hb
    | true =>
      simp only [d17245, d163038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17246 q = 1) (hb : d162092 q = 1) : d163039 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17246, d163039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17246, d163039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17247 q = 1) (hb : d162092 q = 1) : d163040 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17247, d163040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17247, d163040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17248 q = 1) (hb : d162092 q = 1) : d163041 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17248, d163041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17248, d163041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17249 q = 1) (hb : d162092 q = 1) : d163042 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17249, d163042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17249, d163042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17250 q = 1) (hb : d162092 q = 1) : d163043 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17250, d163043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17250, d163043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52546 (p : Pattern) (ha : d17299 p = 1) (hb : d162092 p = 1) : d162972 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17162 q = 1) (hb : d162092 q = 1) : d162960 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, d162960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52518 q ha hb
    | true =>
      simp only [d17162, d162960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52519 q ha hb
  have h2 (q : Pattern) (ha : d17163 q = 1) (hb : d162092 q = 1) : d162961 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17163, d162961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17163, d162961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17164 q = 1) (hb : d162092 q = 1) : d162962 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17164, d162962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17164, d162962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17165 q = 1) (hb : d162092 q = 1) : d162963 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, d162963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52519 q ha hb
    | true =>
      simp only [d17165, d162963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52516 q ha hb
  have h5 (q : Pattern) (ha : d17166 q = 1) (hb : d162092 q = 1) : d162964 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17166, d162964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17166, d162964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17167 q = 1) (hb : d162092 q = 1) : d162965 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17167, d162965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17167, d162965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17168 q = 1) (hb : d162092 q = 1) : d162966 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17168, d162966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17168, d162966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13614 q = 1) (hb : d162092 q = 1) : d13614 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d17294 q = 1) (hb : d162092 q = 1) : d162967 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17294, d162967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52519 q ha hb
    | true =>
      simp only [d17294, d162967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17295 q = 1) (hb : d162092 q = 1) : d162968 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17295, d162968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17295, d162968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17296 q = 1) (hb : d162092 q = 1) : d162969 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17296, d162969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17296, d162969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17297 q = 1) (hb : d162092 q = 1) : d162970 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17297, d162970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17297, d162970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d17298 q = 1) (hb : d162092 q = 1) : d162971 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17298, d162971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17298, d162971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17299 q = 1) (hb : d162092 q = 1) : d162972 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17299, d162972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d17299, d162972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro52547 (p : Pattern) (ha : d17305 p = 1) (hb : d162092 p = 1) : d163053 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17300 q = 1) (hb : d162092 q = 1) : d162973 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17300, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52546 q ha hb
    | true =>
      simp only [d17300, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17301 q = 1) (hb : d162092 q = 1) : d162974 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17301, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17301, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17302 q = 1) (hb : d162092 q = 1) : d163050 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17302, d163050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17302, d163050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17303 q = 1) (hb : d162092 q = 1) : d163051 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17303, d163051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17303, d163051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17304 q = 1) (hb : d162092 q = 1) : d163052 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17304, d163052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17304, d163052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17305 q = 1) (hb : d162092 q = 1) : d163053 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17305, d163053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17305, d163053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52548 (p : Pattern) (ha : d128400 p = 1) (hb : d162092 p = 1) : d163059 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17212 q = 1) (hb : d162092 q = 1) : d163010 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17212, d163010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52538 q ha hb
    | true =>
      simp only [d17212, d163010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52539 q ha hb
  have h2 (q : Pattern) (ha : d17213 q = 1) (hb : d162092 q = 1) : d163011 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17213, d163011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17213, d163011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17214 q = 1) (hb : d162092 q = 1) : d163012 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17214, d163012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17214, d163012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17215 q = 1) (hb : d162092 q = 1) : d163013 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17215, d163013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17215, d163013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17222 q = 1) (hb : d162092 q = 1) : d163020 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17222, d163020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52540 q ha hb
    | true =>
      simp only [d17222, d163020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52541 q ha hb
  have h6 (q : Pattern) (ha : d17223 q = 1) (hb : d162092 q = 1) : d163021 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17223, d163021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17223, d163021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17224 q = 1) (hb : d162092 q = 1) : d163022 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17224, d163022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17224, d163022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17255 q = 1) (hb : d162092 q = 1) : d163048 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17255, d163048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52545 q ha hb
    | true =>
      simp only [d17255, d163048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52529 q ha hb
  have h9 (q : Pattern) (ha : d128396 q = 1) (hb : d162092 q = 1) : d163049 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128396, d163049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128396, d163049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d17306 q = 1) (hb : d162092 q = 1) : d163054 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17306, d163054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52547 q ha hb
    | true =>
      simp only [d17306, d163054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d17307 q = 1) (hb : d162092 q = 1) : d163055 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17307, d163055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17307, d163055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128397 q = 1) (hb : d162092 q = 1) : d163056 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128397, d163056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128397, d163056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128398 q = 1) (hb : d162092 q = 1) : d163057 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128398, d163057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128398, d163057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128399 q = 1) (hb : d162092 q = 1) : d163058 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128399, d163058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128399, d163058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128400 q = 1) (hb : d162092 q = 1) : d163059 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128400, d163059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128400, d163059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro52549 (p : Pattern) (ha : d17312 p = 1) (hb : d162092 p = 1) : d163060 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17175 q = 1) (hb : d162092 q = 1) : d162973 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17175, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52520 q ha hb
    | true =>
      simp only [d17175, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17176 q = 1) (hb : d162092 q = 1) : d162974 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17176, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17176, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d162092 q = 1) : d162977 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52521 q ha hb
    | true =>
      simp only [d17179, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d162092 q = 1) : d162978 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17181 q = 1) (hb : d162092 q = 1) : d162979 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17181, d162979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17181, d162979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17182 q = 1) (hb : d162092 q = 1) : d162980 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17182, d162980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17182, d162980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17208 q = 1) (hb : d162092 q = 1) : d163006 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17208, d163006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17208, d163006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17312 q = 1) (hb : d162092 q = 1) : d163060 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17312, d163060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17312, d163060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro52550 (p : Pattern) (ha : d17313 p = 1) (hb : d162092 p = 1) : d163061 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17179 q = 1) (hb : d162092 q = 1) : d162977 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52521 q ha hb
    | true =>
      simp only [d17179, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17180 q = 1) (hb : d162092 q = 1) : d162978 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17185 q = 1) (hb : d162092 q = 1) : d162983 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17185, d162983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17185, d162983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17186 q = 1) (hb : d162092 q = 1) : d162984 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17186, d162984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17186, d162984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17210 q = 1) (hb : d162092 q = 1) : d163008 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17210, d163008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17210, d163008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17313 q = 1) (hb : d162092 q = 1) : d163061 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17313, d163061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17313, d163061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52551 (p : Pattern) (ha : d17318 p = 1) (hb : d162092 p = 1) : d163066 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17175 q = 1) (hb : d162092 q = 1) : d162973 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17175, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52520 q ha hb
    | true =>
      simp only [d17175, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17176 q = 1) (hb : d162092 q = 1) : d162974 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17176, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17176, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d162092 q = 1) : d162977 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52521 q ha hb
    | true =>
      simp only [d17179, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d162092 q = 1) : d162978 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17181 q = 1) (hb : d162092 q = 1) : d162979 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17181, d162979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17181, d162979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17216 q = 1) (hb : d162092 q = 1) : d163014 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17216, d163014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17216, d163014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17217 q = 1) (hb : d162092 q = 1) : d163015 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17217, d163015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17217, d163015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17318 q = 1) (hb : d162092 q = 1) : d163066 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17318, d163066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17318, d163066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro52552 (p : Pattern) (ha : d17319 p = 1) (hb : d162092 p = 1) : d163067 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17179 q = 1) (hb : d162092 q = 1) : d162977 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52521 q ha hb
    | true =>
      simp only [d17179, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17180 q = 1) (hb : d162092 q = 1) : d162978 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17185 q = 1) (hb : d162092 q = 1) : d162983 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17185, d162983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17185, d162983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17219 q = 1) (hb : d162092 q = 1) : d163017 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17219, d163017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17219, d163017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17220 q = 1) (hb : d162092 q = 1) : d163018 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17220, d163018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17220, d163018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17319 q = 1) (hb : d162092 q = 1) : d163067 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17319, d163067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17319, d163067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52553 (p : Pattern) (ha : d17323 p = 1) (hb : d162092 p = 1) : d163071 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17240 q = 1) (hb : d162092 q = 1) : d163033 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17240, d163033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52544 q ha hb
    | true =>
      simp only [d17240, d163033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17241 q = 1) (hb : d162092 q = 1) : d163034 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17241, d163034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17241, d163034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17245 q = 1) (hb : d162092 q = 1) : d163038 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17245, d163038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52528 q ha hb
    | true =>
      simp only [d17245, d163038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17246 q = 1) (hb : d162092 q = 1) : d163039 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17246, d163039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17246, d163039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17247 q = 1) (hb : d162092 q = 1) : d163040 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17247, d163040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17247, d163040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17248 q = 1) (hb : d162092 q = 1) : d163041 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17248, d163041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17248, d163041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17249 q = 1) (hb : d162092 q = 1) : d163042 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17249, d163042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17249, d163042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17323 q = 1) (hb : d162092 q = 1) : d163071 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17323, d163071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17323, d163071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro52554 (p : Pattern) (ha : d17324 p = 1) (hb : d162092 p = 1) : d163072 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17245 q = 1) (hb : d162092 q = 1) : d163038 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17245, d163038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52528 q ha hb
    | true =>
      simp only [d17245, d163038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17246 q = 1) (hb : d162092 q = 1) : d163039 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17246, d163039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17246, d163039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d162092 q = 1) : d162977 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52521 q ha hb
    | true =>
      simp only [d17179, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d162092 q = 1) : d162978 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17251 q = 1) (hb : d162092 q = 1) : d163044 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17251, d163044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17251, d163044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17252 q = 1) (hb : d162092 q = 1) : d163045 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17252, d163045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17252, d163045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17253 q = 1) (hb : d162092 q = 1) : d163046 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17253, d163046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17253, d163046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17324 q = 1) (hb : d162092 q = 1) : d163072 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17324, d163072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17324, d163072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro52555 (p : Pattern) (ha : d17330 p = 1) (hb : d162092 p = 1) : d163075 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17300 q = 1) (hb : d162092 q = 1) : d162973 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17300, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52546 q ha hb
    | true =>
      simp only [d17300, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17301 q = 1) (hb : d162092 q = 1) : d162974 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17301, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17301, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17302 q = 1) (hb : d162092 q = 1) : d163050 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17302, d163050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17302, d163050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17303 q = 1) (hb : d162092 q = 1) : d163051 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17303, d163051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17303, d163051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17304 q = 1) (hb : d162092 q = 1) : d163052 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17304, d163052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17304, d163052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17330 q = 1) (hb : d162092 q = 1) : d163075 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17330, d163075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17330, d163075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52556 (p : Pattern) (ha : d128405 p = 1) (hb : d162092 p = 1) : d163081 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17212 q = 1) (hb : d162092 q = 1) : d163010 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17212, d163010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52538 q ha hb
    | true =>
      simp only [d17212, d163010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52539 q ha hb
  have h2 (q : Pattern) (ha : d17213 q = 1) (hb : d162092 q = 1) : d163011 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17213, d163011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17213, d163011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17214 q = 1) (hb : d162092 q = 1) : d163012 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17214, d163012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17214, d163012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17215 q = 1) (hb : d162092 q = 1) : d163013 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17215, d163013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17215, d163013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17222 q = 1) (hb : d162092 q = 1) : d163020 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17222, d163020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52540 q ha hb
    | true =>
      simp only [d17222, d163020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52541 q ha hb
  have h6 (q : Pattern) (ha : d17223 q = 1) (hb : d162092 q = 1) : d163021 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17223, d163021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17223, d163021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17224 q = 1) (hb : d162092 q = 1) : d163022 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17224, d163022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17224, d163022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17255 q = 1) (hb : d162092 q = 1) : d163048 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17255, d163048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52545 q ha hb
    | true =>
      simp only [d17255, d163048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52529 q ha hb
  have h9 (q : Pattern) (ha : d128396 q = 1) (hb : d162092 q = 1) : d163049 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128396, d163049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128396, d163049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d17306 q = 1) (hb : d162092 q = 1) : d163054 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17306, d163054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52547 q ha hb
    | true =>
      simp only [d17306, d163054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d17307 q = 1) (hb : d162092 q = 1) : d163055 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17307, d163055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17307, d163055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128397 q = 1) (hb : d162092 q = 1) : d163056 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128397, d163056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128397, d163056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128398 q = 1) (hb : d162092 q = 1) : d163057 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128398, d163057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128398, d163057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128399 q = 1) (hb : d162092 q = 1) : d163058 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128399, d163058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128399, d163058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17314 q = 1) (hb : d162092 q = 1) : d163062 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17314, d163062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52549 q ha hb
    | true =>
      simp only [d17314, d163062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52550 q ha hb
  have h16 (q : Pattern) (ha : d17315 q = 1) (hb : d162092 q = 1) : d163063 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17315, d163063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17315, d163063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d17316 q = 1) (hb : d162092 q = 1) : d163064 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17316, d163064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17316, d163064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d17317 q = 1) (hb : d162092 q = 1) : d163065 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17317, d163065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17317, d163065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d17320 q = 1) (hb : d162092 q = 1) : d163068 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17320, d163068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52551 q ha hb
    | true =>
      simp only [d17320, d163068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52552 q ha hb
  have h20 (q : Pattern) (ha : d17321 q = 1) (hb : d162092 q = 1) : d163069 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17321, d163069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17321, d163069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d17322 q = 1) (hb : d162092 q = 1) : d163070 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17322, d163070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d17322, d163070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d17325 q = 1) (hb : d162092 q = 1) : d163073 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17325, d163073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52553 q ha hb
    | true =>
      simp only [d17325, d163073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52554 q ha hb
  have h23 (q : Pattern) (ha : d128401 q = 1) (hb : d162092 q = 1) : d163074 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128401, d163074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128401, d163074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d17331 q = 1) (hb : d162092 q = 1) : d163076 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17331, d163076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52555 q ha hb
    | true =>
      simp only [d17331, d163076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d17332 q = 1) (hb : d162092 q = 1) : d163077 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17332, d163077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d17332, d163077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d128402 q = 1) (hb : d162092 q = 1) : d163078 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128402, d163078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d128402, d163078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d128403 q = 1) (hb : d162092 q = 1) : d163079 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128403, d163079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128403, d163079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d128404 q = 1) (hb : d162092 q = 1) : d163080 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128404, d163080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128404, d163080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d128405 q = 1) (hb : d162092 q = 1) : d163081 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128405, d163081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128405, d163081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro52557 (p : Pattern) (ha : d128412 p = 1) (hb : d162092 p = 1) : d163106 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17325 q = 1) (hb : d162092 q = 1) : d163073 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17325, d163073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52553 q ha hb
    | true =>
      simp only [d17325, d163073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52554 q ha hb
  have h2 (q : Pattern) (ha : d128401 q = 1) (hb : d162092 q = 1) : d163074 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128401, d163074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128401, d163074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17331 q = 1) (hb : d162092 q = 1) : d163076 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17331, d163076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52555 q ha hb
    | true =>
      simp only [d17331, d163076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17332 q = 1) (hb : d162092 q = 1) : d163077 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17332, d163077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17332, d163077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128402 q = 1) (hb : d162092 q = 1) : d163078 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128402, d163078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128402, d163078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128410 q = 1) (hb : d162092 q = 1) : d163104 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128410, d163104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128410, d163104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128411 q = 1) (hb : d162092 q = 1) : d163105 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128411, d163105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128411, d163105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128412 q = 1) (hb : d162092 q = 1) : d163106 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128412, d163106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128412, d163106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52558 (p : Pattern) (ha : d15795 p = 1) (hb : d162092 p = 1) : d6648 p = 1 := by
  have h0 (q : Pattern) (ha : d6647 q = 1) (hb : d162091 q = 1) : d6647 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15794 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15795 q = 1) (hb : d162092 q = 1) : d6648 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15795, d162092, d6648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15795, d162092, d6648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro52559 (p : Pattern) (ha : d17375 p = 1) (hb : d162092 p = 1) : d163114 p = 1 := by
  have h0 (q : Pattern) (ha : d17373 q = 1) (hb : d162091 q = 1) : d17373 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17374 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17375 q = 1) (hb : d162092 q = 1) : d163114 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17375, d162092, d163114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17375, d162092, d163114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro52560 (p : Pattern) (ha : d17382 p = 1) (hb : d162092 p = 1) : d163115 p = 1 := by
  have h0 (q : Pattern) (ha : d17380 q = 1) (hb : d162091 q = 1) : d17380 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17381 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17382 q = 1) (hb : d162092 q = 1) : d163115 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17382, d162092, d163115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17382, d162092, d163115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro52561 (p : Pattern) (ha : d17386 p = 1) (hb : d162092 p = 1) : d13822 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d13816 q = 1) : d13816 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15775 q = 1) (hb : d116750 q = 1) : d13817 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15775, d13817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15775, d13817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37057 q ha hb
  have h3 (q : Pattern) (ha : d10371 q = 1) (hb : d116750 q = 1) : d13678 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d13678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37057 q ha hb
    | true =>
      simp only [d10371, d13678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d15776 q = 1) (hb : d116750 q = 1) : d13818 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15776, d13818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15776, d13818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10373 q = 1) (hb : d116750 q = 1) : d13679 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, d13679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10373, d13679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d15777 q = 1) (hb : d116750 q = 1) : d13819 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15777, d13819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15777, d13819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15778 q = 1) (hb : d116750 q = 1) : d13820 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15778, d13820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15778, d13820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d17381 q = 1) (hb : d162091 q = 1) : d13821 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17381, d162091, d13821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d17381, d162091, d13821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d15779 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17386 q = 1) (hb : d162092 q = 1) : d13822 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17386, d162092, d13822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17386, d162092, d13822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro52562 (p : Pattern) (ha : d17405 p = 1) (hb : d162092 p = 1) : d163133 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17383 q = 1) (hb : d162092 q = 1) : d163116 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17383, d163116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52559 q ha hb
    | true =>
      simp only [d17383, d163116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52560 q ha hb
  have h2 (q : Pattern) (ha : d17384 q = 1) (hb : d162092 q = 1) : d163117 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17384, d163117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17384, d163117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17385 q = 1) (hb : d162092 q = 1) : d163118 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17385, d163118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17385, d163118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17387 q = 1) (hb : d162092 q = 1) : d163119 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17387, d163119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52560 q ha hb
    | true =>
      simp only [d17387, d163119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52561 q ha hb
  have h5 (q : Pattern) (ha : d17388 q = 1) (hb : d162092 q = 1) : d163120 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17388, d163120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17388, d163120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17389 q = 1) (hb : d162092 q = 1) : d163121 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17389, d163121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17389, d163121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17390 q = 1) (hb : d162092 q = 1) : d163122 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17390, d163122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17390, d163122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17397 q = 1) (hb : d162092 q = 1) : d163125 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d163125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52560 q ha hb
    | true =>
      simp only [d17397, d163125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52534 q ha hb
  have h9 (q : Pattern) (ha : d17398 q = 1) (hb : d162092 q = 1) : d163126 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d163126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d163126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17399 q = 1) (hb : d162092 q = 1) : d163127 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d163127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d163127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17400 q = 1) (hb : d162092 q = 1) : d163128 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d163128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52534 q ha hb
    | true =>
      simp only [d17400, d163128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52558 q ha hb
  have h12 (q : Pattern) (ha : d17401 q = 1) (hb : d162092 q = 1) : d163129 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d163129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d163129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17402 q = 1) (hb : d162092 q = 1) : d163130 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d163130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d163130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17403 q = 1) (hb : d162092 q = 1) : d163131 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d163131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17403, d163131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17404 q = 1) (hb : d162092 q = 1) : d163132 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17404, d163132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17404, d163132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17405 q = 1) (hb : d162092 q = 1) : d163133 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17405, d163133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d17405, d163133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro52563 (p : Pattern) (ha : d17410 p = 1) (hb : d162092 p = 1) : d163138 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17397 q = 1) (hb : d162092 q = 1) : d163125 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d163125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52560 q ha hb
    | true =>
      simp only [d17397, d163125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52534 q ha hb
  have h2 (q : Pattern) (ha : d17398 q = 1) (hb : d162092 q = 1) : d163126 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d163126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d163126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17399 q = 1) (hb : d162092 q = 1) : d163127 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d163127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d163127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17400 q = 1) (hb : d162092 q = 1) : d163128 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d163128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52534 q ha hb
    | true =>
      simp only [d17400, d163128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52558 q ha hb
  have h5 (q : Pattern) (ha : d17401 q = 1) (hb : d162092 q = 1) : d163129 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d163129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d163129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17402 q = 1) (hb : d162092 q = 1) : d163130 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d163130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d163130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17403 q = 1) (hb : d162092 q = 1) : d163131 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d163131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17403, d163131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17408 q = 1) (hb : d162092 q = 1) : d163136 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17408, d163136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17408, d163136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17409 q = 1) (hb : d162092 q = 1) : d163137 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17409, d163137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17409, d163137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17410 q = 1) (hb : d162092 q = 1) : d163138 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17410, d163138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17410, d163138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro52564 (p : Pattern) (ha : d17416 p = 1) (hb : d162092 p = 1) : d163144 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17406 q = 1) (hb : d162092 q = 1) : d163134 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17406, d163134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52562 q ha hb
    | true =>
      simp only [d17406, d163134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17407 q = 1) (hb : d162092 q = 1) : d163135 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17407, d163135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17407, d163135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17411 q = 1) (hb : d162092 q = 1) : d163139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17411, d163139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52563 q ha hb
    | true =>
      simp only [d17411, d163139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17412 q = 1) (hb : d162092 q = 1) : d163140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17412, d163140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17412, d163140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17413 q = 1) (hb : d162092 q = 1) : d163141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17413, d163141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17413, d163141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17414 q = 1) (hb : d162092 q = 1) : d163142 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17414, d163142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17414, d163142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17415 q = 1) (hb : d162092 q = 1) : d163143 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17415, d163143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17415, d163143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17416 q = 1) (hb : d162092 q = 1) : d163144 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17416, d163144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17416, d163144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro52565 (p : Pattern) (ha : d17428 p = 1) (hb : d162092 p = 1) : d163156 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17411 q = 1) (hb : d162092 q = 1) : d163139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17411, d163139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52563 q ha hb
    | true =>
      simp only [d17411, d163139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17412 q = 1) (hb : d162092 q = 1) : d163140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17412, d163140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17412, d163140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17423 q = 1) (hb : d162092 q = 1) : d163151 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17423, d163151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52535 q ha hb
    | true =>
      simp only [d17423, d163151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17424 q = 1) (hb : d162092 q = 1) : d163152 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17424, d163152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17424, d163152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17425 q = 1) (hb : d162092 q = 1) : d163153 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17425, d163153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17425, d163153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17426 q = 1) (hb : d162092 q = 1) : d163154 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17426, d163154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17426, d163154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17427 q = 1) (hb : d162092 q = 1) : d163155 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17427, d163155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17427, d163155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17428 q = 1) (hb : d162092 q = 1) : d163156 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17428, d163156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17428, d163156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro52566 (p : Pattern) (ha : d17477 p = 1) (hb : d162092 p = 1) : d163160 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17397 q = 1) (hb : d162092 q = 1) : d163125 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d163125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52560 q ha hb
    | true =>
      simp only [d17397, d163125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52534 q ha hb
  have h2 (q : Pattern) (ha : d17398 q = 1) (hb : d162092 q = 1) : d163126 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d163126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d163126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17399 q = 1) (hb : d162092 q = 1) : d163127 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d163127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d163127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17400 q = 1) (hb : d162092 q = 1) : d163128 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d163128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52534 q ha hb
    | true =>
      simp only [d17400, d163128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52558 q ha hb
  have h5 (q : Pattern) (ha : d17401 q = 1) (hb : d162092 q = 1) : d163129 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d163129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d163129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17402 q = 1) (hb : d162092 q = 1) : d163130 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d163130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d163130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17403 q = 1) (hb : d162092 q = 1) : d163131 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d163131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17403, d163131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13843 q = 1) (hb : d162092 q = 1) : d13843 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d17472 q = 1) (hb : d162092 q = 1) : d163145 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17472, d163145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52534 q ha hb
    | true =>
      simp only [d17472, d163145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17473 q = 1) (hb : d162092 q = 1) : d163146 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17473, d163146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17473, d163146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17474 q = 1) (hb : d162092 q = 1) : d163147 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17474, d163147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17474, d163147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17475 q = 1) (hb : d162092 q = 1) : d163148 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17475, d163148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17475, d163148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d17476 q = 1) (hb : d162092 q = 1) : d163159 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17476, d163159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17476, d163159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17477 q = 1) (hb : d162092 q = 1) : d163160 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17477, d163160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d17477, d163160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro52567 (p : Pattern) (ha : d17483 p = 1) (hb : d162092 p = 1) : d163166 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17478 q = 1) (hb : d162092 q = 1) : d163161 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17478, d163161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52566 q ha hb
    | true =>
      simp only [d17478, d163161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17479 q = 1) (hb : d162092 q = 1) : d163162 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17479, d163162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17479, d163162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17480 q = 1) (hb : d162092 q = 1) : d163163 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17480, d163163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17480, d163163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17481 q = 1) (hb : d162092 q = 1) : d163164 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17481, d163164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17481, d163164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17482 q = 1) (hb : d162092 q = 1) : d163165 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17482, d163165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17482, d163165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17483 q = 1) (hb : d162092 q = 1) : d163166 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17483, d163166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17483, d163166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52568 (p : Pattern) (ha : d128422 p = 1) (hb : d162092 p = 1) : d163172 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17429 q = 1) (hb : d162092 q = 1) : d163157 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17429, d163157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52564 q ha hb
    | true =>
      simp only [d17429, d163157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52565 q ha hb
  have h2 (q : Pattern) (ha : d128418 q = 1) (hb : d162092 q = 1) : d163158 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128418, d163158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128418, d163158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17484 q = 1) (hb : d162092 q = 1) : d163167 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17484, d163167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52567 q ha hb
    | true =>
      simp only [d17484, d163167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17485 q = 1) (hb : d162092 q = 1) : d163168 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17485, d163168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17485, d163168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128419 q = 1) (hb : d162092 q = 1) : d163169 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128419, d163169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128419, d163169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128420 q = 1) (hb : d162092 q = 1) : d163170 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128420, d163170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128420, d163170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128421 q = 1) (hb : d162092 q = 1) : d163171 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128421, d163171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128421, d163171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128422 q = 1) (hb : d162092 q = 1) : d163172 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128422, d163172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128422, d163172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52569 (p : Pattern) (ha : d128428 p = 1) (hb : d162092 p = 1) : d163189 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17195 q = 1) (hb : d162092 q = 1) : d162993 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17195, d162993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17195, d162993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52524 q ha hb
  have h2 (q : Pattern) (ha : d17196 q = 1) (hb : d162092 q = 1) : d162994 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d17196, d162994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17196, d162994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17205 q = 1) (hb : d162092 q = 1) : d163003 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17205, d163003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52524 q ha hb
    | true =>
      simp only [d17205, d163003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52527 q ha hb
  have h4 (q : Pattern) (ha : d17206 q = 1) (hb : d162092 q = 1) : d163004 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d17206, d163004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17206, d163004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17207 q = 1) (hb : d162092 q = 1) : d163005 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d17207, d163005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17207, d163005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128406 q = 1) (hb : d162092 q = 1) : d163082 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128406, d163082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52548 q ha hb
    | true =>
      simp only [d128406, d163082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52556 q ha hb
  have h7 (q : Pattern) (ha : d17355 q = 1) (hb : d162092 q = 1) : d163100 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17355, d163100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52530 q ha hb
    | true =>
      simp only [d17355, d163100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52531 q ha hb
  have h8 (q : Pattern) (ha : d128407 q = 1) (hb : d162092 q = 1) : d163101 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128407, d163101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128407, d163101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128408 q = 1) (hb : d162092 q = 1) : d163102 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128408, d163102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128408, d163102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d128409 q = 1) (hb : d162092 q = 1) : d163103 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128409, d163103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128409, d163103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128413 q = 1) (hb : d162092 q = 1) : d163107 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128413, d163107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128413, d163107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52557 q ha hb
  have h12 (q : Pattern) (ha : d17364 q = 1) (hb : d162092 q = 1) : d163109 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17364, d163109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17364, d163109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52532 q ha hb
  have h13 (q : Pattern) (ha : d128414 q = 1) (hb : d162092 q = 1) : d163110 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128414, d163110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128414, d163110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128415 q = 1) (hb : d162092 q = 1) : d163111 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128415, d163111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128415, d163111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d128416 q = 1) (hb : d162092 q = 1) : d163112 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128416, d163112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128416, d163112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d128417 q = 1) (hb : d162092 q = 1) : d163113 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128417, d163113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128417, d163113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128423 q = 1) (hb : d162092 q = 1) : d163173 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128423, d163173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128423, d163173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52568 q ha hb
  have h18 (q : Pattern) (ha : d17501 q = 1) (hb : d162092 q = 1) : d163184 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17501, d163184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17501, d163184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52537 q ha hb
  have h19 (q : Pattern) (ha : d128424 q = 1) (hb : d162092 q = 1) : d163185 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128424, d163185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128424, d163185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d128425 q = 1) (hb : d162092 q = 1) : d163186 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128425, d163186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d128425, d163186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d128426 q = 1) (hb : d162092 q = 1) : d163187 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128426, d163187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128426, d163187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d128427 q = 1) (hb : d162092 q = 1) : d163188 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128427, d163188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128427, d163188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d128428 q = 1) (hb : d162092 q = 1) : d163189 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128428, d163189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128428, d163189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro52570 (p : Pattern) (ha : d128434 p = 1) (hb : d162092 p = 1) : d163195 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128429 q = 1) (hb : d162092 q = 1) : d163190 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128429, d163190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128429, d163190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52569 q ha hb
  have h2 (q : Pattern) (ha : d128430 q = 1) (hb : d162092 q = 1) : d163191 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128430, d163191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128430, d163191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128431 q = 1) (hb : d162092 q = 1) : d163192 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128431, d163192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128431, d163192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128432 q = 1) (hb : d162092 q = 1) : d163193 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128432, d163193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128432, d163193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128433 q = 1) (hb : d162092 q = 1) : d163194 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128433, d163194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128433, d163194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128434 q = 1) (hb : d162092 q = 1) : d163195 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128434, d163195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128434, d163195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52571 (p : Pattern) (ha : d128440 p = 1) (hb : d162092 p = 1) : d163201 p = 1 := by
  have h0 (q : Pattern) (ha : d128269 q = 1) (hb : d162092 q = 1) : d162312 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128269, d162312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52317 q ha hb
    | true =>
      simp only [d128269, d162312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52359 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128309 q = 1) (hb : d162092 q = 1) : d162464 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128309, d162464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128309, d162464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52405 q ha hb
  have h3 (q : Pattern) (ha : d128310 q = 1) (hb : d162092 q = 1) : d162465 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128310, d162465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128310, d162465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128350 q = 1) (hb : d162092 q = 1) : d162709 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128350, d162709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128350, d162709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52460 q ha hb
  have h5 (q : Pattern) (ha : d128351 q = 1) (hb : d162092 q = 1) : d162710 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128351, d162710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128351, d162710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128352 q = 1) (hb : d162092 q = 1) : d162711 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128352, d162711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128352, d162711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128392 q = 1) (hb : d162092 q = 1) : d162953 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128392, d162953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128392, d162953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52515 q ha hb
  have h8 (q : Pattern) (ha : d128393 q = 1) (hb : d162092 q = 1) : d162954 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128393, d162954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128393, d162954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128394 q = 1) (hb : d162092 q = 1) : d162955 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128394, d162955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128394, d162955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128395 q = 1) (hb : d162092 q = 1) : d162956 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d128395, d162956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128395, d162956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128435 q = 1) (hb : d162092 q = 1) : d163196 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128435, d163196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128435, d163196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52570 q ha hb
  have h12 (q : Pattern) (ha : d128436 q = 1) (hb : d162092 q = 1) : d163197 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128436, d163197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128436, d163197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128437 q = 1) (hb : d162092 q = 1) : d163198 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128437, d163198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128437, d163198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128438 q = 1) (hb : d162092 q = 1) : d163199 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d128438, d163199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128438, d163199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128439 q = 1) (hb : d162092 q = 1) : d163200 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d128439, d163200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128439, d163200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128440 q = 1) (hb : d162092 q = 1) : d163201 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d128440, d163201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128440, d163201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro52572 (p : Pattern) (ha : d128446 p = 1) (hb : d162092 p = 1) : d163207 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128441 q = 1) (hb : d162092 q = 1) : d163202 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d128441, d163202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52571 q ha hb
    | true =>
      simp only [d128441, d163202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128442 q = 1) (hb : d162092 q = 1) : d163203 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d128442, d163203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128442, d163203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128443 q = 1) (hb : d162092 q = 1) : d163204 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d128443, d163204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128443, d163204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128444 q = 1) (hb : d162092 q = 1) : d163205 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d128444, d163205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128444, d163205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128445 q = 1) (hb : d162092 q = 1) : d163206 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d128445, d163206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128445, d163206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128446 q = 1) (hb : d162092 q = 1) : d163207 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d128446, d163207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128446, d163207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52573 (p : Pattern) (ha : d128452 p = 1) (hb : d162092 p = 1) : d163213 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128447 q = 1) (hb : d162092 q = 1) : d163208 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d128447, d163208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52572 q ha hb
    | true =>
      simp only [d128447, d163208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128448 q = 1) (hb : d162092 q = 1) : d163209 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d128448, d163209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128448, d163209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128449 q = 1) (hb : d162092 q = 1) : d163210 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d128449, d163210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128449, d163210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128450 q = 1) (hb : d162092 q = 1) : d163211 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d128450, d163211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128450, d163211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128451 q = 1) (hb : d162092 q = 1) : d163212 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d128451, d163212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128451, d163212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128452 q = 1) (hb : d162092 q = 1) : d163213 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d128452, d163213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128452, d163213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52574 (p : Pattern) (ha : d128458 p = 1) (hb : d162095 p = 1) : d163219 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128453 q = 1) (hb : d162092 q = 1) : d163214 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d128453, d163214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52573 q ha hb
    | true =>
      simp only [d128453, d163214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128454 q = 1) (hb : d162092 q = 1) : d163215 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d128454, d163215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128454, d163215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128455 q = 1) (hb : d162092 q = 1) : d163216 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d128455, d163216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128455, d163216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128456 q = 1) (hb : d162092 q = 1) : d163217 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d128456, d163217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128456, d163217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128457 q = 1) (hb : d162092 q = 1) : d163218 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d128457, d163218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128457, d163218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d128458 q = 1) (hb : d162095 q = 1) : d163219 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d128458, d162095, d163219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128458, d162095, d163219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro52575 (p : Pattern) (ha : d128464 p = 1) (hb : d162095 p = 1) : d163225 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162095 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128459 q = 1) (hb : d162095 q = 1) : d163220 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d128459, d163220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52574 q ha hb
    | true =>
      simp only [d128459, d163220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128460 q = 1) (hb : d162095 q = 1) : d163221 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d128460, d163221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128460, d163221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128461 q = 1) (hb : d162095 q = 1) : d163222 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d128461, d163222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128461, d163222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128462 q = 1) (hb : d162095 q = 1) : d163223 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d128462, d163223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128462, d163223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128463 q = 1) (hb : d162095 q = 1) : d163224 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d128463, d163224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128463, d163224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128464 q = 1) (hb : d162095 q = 1) : d163225 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d128464, d163225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128464, d163225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52576 (p : Pattern) (ha : d128470 p = 1) (hb : d162095 p = 1) : d163231 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162095 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128465 q = 1) (hb : d162095 q = 1) : d163226 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d128465, d163226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52575 q ha hb
    | true =>
      simp only [d128465, d163226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128466 q = 1) (hb : d162095 q = 1) : d163227 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d128466, d163227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128466, d163227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128467 q = 1) (hb : d162095 q = 1) : d163228 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d128467, d163228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128467, d163228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128468 q = 1) (hb : d162095 q = 1) : d163229 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d128468, d163229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128468, d163229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128469 q = 1) (hb : d162095 q = 1) : d163230 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d128469, d163230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128469, d163230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128470 q = 1) (hb : d162095 q = 1) : d163231 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d128470, d163231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128470, d163231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52577 (p : Pattern) (ha : d128476 p = 1) (hb : d162095 p = 1) : d163237 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162095 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128471 q = 1) (hb : d162095 q = 1) : d163232 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d128471, d163232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52576 q ha hb
    | true =>
      simp only [d128471, d163232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128472 q = 1) (hb : d162095 q = 1) : d163233 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d128472, d163233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128472, d163233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128473 q = 1) (hb : d162095 q = 1) : d163234 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d128473, d163234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128473, d163234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128474 q = 1) (hb : d162095 q = 1) : d163235 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d128474, d163235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128474, d163235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128475 q = 1) (hb : d162095 q = 1) : d163236 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d128475, d163236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128475, d163236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128476 q = 1) (hb : d162095 q = 1) : d163237 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d128476, d163237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128476, d163237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52578 (p : Pattern) (ha : d128482 p = 1) (hb : d162095 p = 1) : d163243 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162095 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128477 q = 1) (hb : d162095 q = 1) : d163238 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d128477, d163238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52577 q ha hb
    | true =>
      simp only [d128477, d163238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128478 q = 1) (hb : d162095 q = 1) : d163239 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d128478, d163239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128478, d163239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128479 q = 1) (hb : d162095 q = 1) : d163240 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d128479, d163240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128479, d163240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128480 q = 1) (hb : d162095 q = 1) : d163241 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d128480, d163241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128480, d163241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128481 q = 1) (hb : d162095 q = 1) : d163242 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d128481, d163242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128481, d163242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128482 q = 1) (hb : d162095 q = 1) : d163243 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d128482, d163243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128482, d163243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52579 (p : Pattern) (ha : d12227 p = 1) (hb : d112691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4819 q = 1) (hb : d68915 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d68915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7917 q ha hb
    | true =>
      simp only [d4819, d68915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
  have h2 (q : Pattern) (ha : d4820 q = 1) (hb : d68916 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d68916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4820, d68916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4821 q = 1) (hb : d68917 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d68917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4821, d68917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31 q = 1) (hb : d51883 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
    | true =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32 q = 1) (hb : d51884 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33 q = 1) (hb : d51885 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12225 q = 1) (hb : d112689 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12225, d112689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12225, d112689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d34 q = 1) (hb : d51886 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, d51886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34, d51886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12226 q = 1) (hb : d112690 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12226, d112690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12226, d112690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12227 q = 1) (hb : d112691 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12227, d112691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12227, d112691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro52580 (p : Pattern) (ha : d12233 p = 1) (hb : d112697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d112692 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d112692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52579 q ha hb
    | true =>
      simp only [d12228, d112692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d112693 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d112693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d112693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12230 q = 1) (hb : d112694 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d112694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d112694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12231 q = 1) (hb : d112695 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12231, d112695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12231, d112695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12232 q = 1) (hb : d112696 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12232, d112696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12232, d112696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12233 q = 1) (hb : d112697 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12233, d112697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12233, d112697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52581 (p : Pattern) (ha : d112703 p = 1) (hb : d115242 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d51969 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
    | true =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d51970 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d51971 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d51976 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
    | true =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d51977 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12234 q = 1) (hb : d112698 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d112698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52580 q ha hb
    | true =>
      simp only [d12234, d112698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d112699 q = 1) (hb : d115238 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112699, d115238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d112699, d115238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d112700 q = 1) (hb : d115239 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112700, d115239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d112700, d115239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d112701 q = 1) (hb : d115240 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112701, d115240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d112701, d115240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d112702 q = 1) (hb : d115241 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112702, d115241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d112702, d115241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d112703 q = 1) (hb : d115242 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112703, d115242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112703, d115242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro52582 (p : Pattern) (ha : d12240 p = 1) (hb : d112704 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d112692 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d112692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52579 q ha hb
    | true =>
      simp only [d12228, d112692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d112693 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d112693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d112693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12230 q = 1) (hb : d112694 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d112694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d112694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12231 q = 1) (hb : d112695 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12231, d112695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12231, d112695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12232 q = 1) (hb : d112696 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12232, d112696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12232, d112696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12240 q = 1) (hb : d112704 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12240, d112704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12240, d112704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro52583 (p : Pattern) (ha : d112710 p = 1) (hb : d115247 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d51969 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
    | true =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d51970 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d51971 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d51976 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
    | true =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d51977 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12234 q = 1) (hb : d112698 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d112698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52580 q ha hb
    | true =>
      simp only [d12234, d112698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d112699 q = 1) (hb : d115238 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112699, d115238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d112699, d115238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d112700 q = 1) (hb : d115239 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112700, d115239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d112700, d115239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d112701 q = 1) (hb : d115240 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112701, d115240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d112701, d115240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d112702 q = 1) (hb : d115241 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112702, d115241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d112702, d115241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d195 q = 1) (hb : d52015 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, d52015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q ha hb
    | true =>
      simp only [d195, d52015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d196 q = 1) (hb : d52016 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, d52016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, d52016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d197 q = 1) (hb : d52017 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, d52017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d197, d52017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d198 q = 1) (hb : d52018 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, d52018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, d52018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d200 q = 1) (hb : d52020 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, d52020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q ha hb
    | true =>
      simp only [d200, d52020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d201 q = 1) (hb : d52021 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, d52021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, d52021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d202 q = 1) (hb : d52022 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, d52022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202, d52022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d12241 q = 1) (hb : d112705 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12241, d112705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52582 q ha hb
    | true =>
      simp only [d12241, d112705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d112706 q = 1) (hb : d115243 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112706, d115243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d112706, d115243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d51 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d112707 q = 1) (hb : d115244 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112707, d115244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d112707, d115244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d112708 q = 1) (hb : d115245 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112708, d115245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d112708, d115245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d112709 q = 1) (hb : d115246 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112709, d115246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d112709, d115246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d112710 q = 1) (hb : d115247 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112710, d115247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d112710, d115247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro52584 (p : Pattern) (ha : d112717 p = 1) (hb : d115254 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12241 q = 1) (hb : d112705 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12241, d112705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52582 q ha hb
    | true =>
      simp only [d12241, d112705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d112706 q = 1) (hb : d115243 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112706, d115243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d112706, d115243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d112707 q = 1) (hb : d115244 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112707, d115244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112707, d115244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d112715 q = 1) (hb : d115252 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112715, d115252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112715, d115252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112716 q = 1) (hb : d115253 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112716, d115253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112716, d115253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112717 q = 1) (hb : d115254 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112717, d115254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112717, d115254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro52585 (p : Pattern) (ha : d12261 p = 1) (hb : d112725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6079 q = 1) (hb : d75841 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d75841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10860 q ha hb
    | true =>
      simp only [d6079, d75841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
  have h2 (q : Pattern) (ha : d6080 q = 1) (hb : d75842 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d75842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6080, d75842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6081 q = 1) (hb : d75843 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d75843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6081, d75843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72 q = 1) (hb : d51924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
    | true =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d73 q = 1) (hb : d51925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12259 q = 1) (hb : d112723 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12259, d112723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12259, d112723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75 q = 1) (hb : d51927 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12260 q = 1) (hb : d112724 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12260, d112724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12260, d112724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12261 q = 1) (hb : d112725 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12261, d112725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12261, d112725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro52586 (p : Pattern) (ha : d12267 p = 1) (hb : d112731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12262 q = 1) (hb : d112726 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12262, d112726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52585 q ha hb
    | true =>
      simp only [d12262, d112726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12263 q = 1) (hb : d112727 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12263, d112727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12263, d112727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78 q = 1) (hb : d51930 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11 q ha hb
    | true =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d79 q = 1) (hb : d51931 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, d51931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, d51931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12264 q = 1) (hb : d112728 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12264, d112728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12264, d112728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12265 q = 1) (hb : d112729 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12265, d112729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12265, d112729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12266 q = 1) (hb : d112730 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12266, d112730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12266, d112730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12267 q = 1) (hb : d112731 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12267, d112731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12267, d112731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro52587 (p : Pattern) (ha : d112737 p = 1) (hb : d115264 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12268 q = 1) (hb : d112732 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12268, d112732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52586 q ha hb
    | true =>
      simp only [d12268, d112732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d112733 q = 1) (hb : d115260 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112733, d115260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d112733, d115260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d84 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
    | true =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85 q = 1) (hb : d51937 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, d51937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85, d51937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d112734 q = 1) (hb : d115261 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112734, d115261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112734, d115261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d112735 q = 1) (hb : d115262 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112735, d115262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112735, d115262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112736 q = 1) (hb : d115263 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112736, d115263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112736, d115263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112737 q = 1) (hb : d115264 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112737, d115264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112737, d115264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro52588 (p : Pattern) (ha : d112743 p = 1) (hb : d115270 p = 1) : d0 p = 1 := by
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
  have h6 (q : Pattern) (ha : d112711 q = 1) (hb : d115248 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112711, d115248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52581 q ha hb
    | true =>
      simp only [d112711, d115248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52583 q ha hb
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
  have h8 (q : Pattern) (ha : d112712 q = 1) (hb : d115249 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112712, d115249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112712, d115249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d112713 q = 1) (hb : d115250 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d112713, d115250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d112713, d115250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d112714 q = 1) (hb : d115251 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d112714, d115251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d112714, d115251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d112718 q = 1) (hb : d115255 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112718, d115255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112718, d115255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52584 q ha hb
  have h12 (q : Pattern) (ha : d112719 q = 1) (hb : d115256 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112719, d115256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d112719, d115256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d112720 q = 1) (hb : d115257 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d112720, d115257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d112720, d115257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d112721 q = 1) (hb : d115258 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d112721, d115258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d112721, d115258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d112722 q = 1) (hb : d115259 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d112722, d115259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d112722, d115259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d112738 q = 1) (hb : d115265 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112738, d115265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112738, d115265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52587 q ha hb
  have h17 (q : Pattern) (ha : d112739 q = 1) (hb : d115266 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112739, d115266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d112739, d115266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d112740 q = 1) (hb : d115267 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d112740, d115267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d112740, d115267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d112741 q = 1) (hb : d115268 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d112741, d115268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d112741, d115268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d112742 q = 1) (hb : d115269 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d112742, d115269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d112742, d115269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d112743 q = 1) (hb : d115270 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d112743, d115270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d112743, d115270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro52589 (p : Pattern) (ha : d12289 p = 1) (hb : d112753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12234 q = 1) (hb : d112698 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d112698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52580 q ha hb
    | true =>
      simp only [d12234, d112698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h2 (q : Pattern) (ha : d12285 q = 1) (hb : d112749 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12285, d112749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12285, d112749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12286 q = 1) (hb : d112750 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12286, d112750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12286, d112750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12287 q = 1) (hb : d112751 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12287, d112751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12287, d112751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12288 q = 1) (hb : d112752 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12288, d112752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12288, d112752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12289 q = 1) (hb : d112753 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12289, d112753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12289, d112753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52590 (p : Pattern) (ha : d12296 p = 1) (hb : d112760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12234 q = 1) (hb : d112698 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d112698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52580 q ha hb
    | true =>
      simp only [d12234, d112698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h2 (q : Pattern) (ha : d12285 q = 1) (hb : d112749 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12285, d112749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12285, d112749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12286 q = 1) (hb : d112750 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12286, d112750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12286, d112750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12287 q = 1) (hb : d112751 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12287, d112751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12287, d112751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12288 q = 1) (hb : d112752 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12288, d112752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12288, d112752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12241 q = 1) (hb : d112705 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12241, d112705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52582 q ha hb
    | true =>
      simp only [d12241, d112705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h7 (q : Pattern) (ha : d12292 q = 1) (hb : d112756 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12292, d112756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12292, d112756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12293 q = 1) (hb : d112757 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12293, d112757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12293, d112757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12294 q = 1) (hb : d112758 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12294, d112758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12294, d112758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12295 q = 1) (hb : d112759 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12295, d112759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12295, d112759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12296 q = 1) (hb : d112760 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12296, d112760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12296, d112760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro52591 (p : Pattern) (ha : d12373 p = 1) (hb : d112821 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12234 q = 1) (hb : d112698 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d112698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52580 q ha hb
    | true =>
      simp only [d12234, d112698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h2 (q : Pattern) (ha : d12285 q = 1) (hb : d112749 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12285, d112749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12285, d112749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12286 q = 1) (hb : d112750 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12286, d112750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12286, d112750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12287 q = 1) (hb : d112751 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12287, d112751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12287, d112751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12288 q = 1) (hb : d112752 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12288, d112752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12288, d112752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d100 q = 1) (hb : d51952 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101 q = 1) (hb : d51953 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d102 q = 1) (hb : d51954 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d51954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, d51954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d103 q = 1) (hb : d51955 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d51955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d51955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12373 q = 1) (hb : d112821 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12373, d112821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12373, d112821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro52592 (p : Pattern) (ha : d12301 p = 1) (hb : d112765 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d112692 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d112692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52579 q ha hb
    | true =>
      simp only [d12228, d112692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d112693 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d112693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d112693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12230 q = 1) (hb : d112694 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d112694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d112694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12231 q = 1) (hb : d112695 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12231, d112695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12231, d112695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12300 q = 1) (hb : d112764 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12300, d112764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12300, d112764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12301 q = 1) (hb : d112765 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12301, d112765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12301, d112765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52593 (p : Pattern) (ha : d12308 p = 1) (hb : d112772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d112692 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d112692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52579 q ha hb
    | true =>
      simp only [d12228, d112692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d112693 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d112693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d112693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12230 q = 1) (hb : d112694 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d112694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d112694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12306 q = 1) (hb : d112770 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12306, d112770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12306, d112770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12307 q = 1) (hb : d112771 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12307, d112771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12307, d112771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12308 q = 1) (hb : d112772 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12308, d112772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12308, d112772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52594 (p : Pattern) (ha : d12344 p = 1) (hb : d112794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d112692 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d112692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52579 q ha hb
    | true =>
      simp only [d12228, d112692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d112693 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d112693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d112693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12341 q = 1) (hb : d112791 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12341, d112791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12341, d112791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12342 q = 1) (hb : d112792 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12342, d112792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12342, d112792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12343 q = 1) (hb : d112793 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12343, d112793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12343, d112793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12344 q = 1) (hb : d112794 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12344, d112794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12344, d112794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52595 (p : Pattern) (ha : d4913 p = 1) (hb : d112776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d320 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321 q = 1) (hb : d52120 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d52121 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d751 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33341 q ha hb
    | true =>
      simp only [d751, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d752 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d752, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d753 q = 1) (hb : d51992 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d51992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d51992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d754 q = 1) (hb : d51993 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d51993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d754, d51993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d755 q = 1) (hb : d52122 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d755, d52122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d755, d52122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4913 q = 1) (hb : d112776 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d4913, d112776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4913, d112776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro52596 (p : Pattern) (ha : d112782 p = 1) (hb : d162101 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112777 q = 1) (hb : d162096 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d112777, d162096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52595 q hb ha
    | true =>
      simp only [d112777, d162096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7917 q hb ha
  have h2 (q : Pattern) (ha : d112778 q = 1) (hb : d162097 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d112778, d162097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112778, d162097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112779 q = 1) (hb : d162098 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d112779, d162098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112779, d162098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4819 q = 1) (hb : d68915 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d68915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7917 q ha hb
    | true =>
      simp only [d4819, d68915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
  have h5 (q : Pattern) (ha : d4820 q = 1) (hb : d68916 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d68916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4820, d68916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4821 q = 1) (hb : d68917 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d68917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4821, d68917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112780 q = 1) (hb : d162099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d112780, d162099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112780, d162099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d31 q = 1) (hb : d51883 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
    | true =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32 q = 1) (hb : d51884 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33 q = 1) (hb : d51885 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12225 q = 1) (hb : d112689 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12225, d112689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12225, d112689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d112781 q = 1) (hb : d162100 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d112781, d162100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112781, d162100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d112782 q = 1) (hb : d162101 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d112782, d162101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d112782, d162101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro52597 (p : Pattern) (ha : d112788 p = 1) (hb : d162107 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112783 q = 1) (hb : d162102 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112783, d162102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52596 q ha hb
    | true =>
      simp only [d112783, d162102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112784 q = 1) (hb : d162103 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112784, d162103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112784, d162103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12228 q = 1) (hb : d112692 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d112692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52579 q ha hb
    | true =>
      simp only [d12228, d112692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12229 q = 1) (hb : d112693 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d112693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d112693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112785 q = 1) (hb : d162104 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112785, d162104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112785, d162104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112786 q = 1) (hb : d162105 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112786, d162105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112786, d162105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112787 q = 1) (hb : d162106 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112787, d162106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112787, d162106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112788 q = 1) (hb : d162107 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112788, d162107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112788, d162107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52598 (p : Pattern) (ha : d112800 p = 1) (hb : d162113 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12302 q = 1) (hb : d112766 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12302, d112766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52592 q ha hb
    | true =>
      simp only [d12302, d112766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
  have h2 (q : Pattern) (ha : d12303 q = 1) (hb : d112767 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12303, d112767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12303, d112767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12304 q = 1) (hb : d112768 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12304, d112768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12304, d112768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12305 q = 1) (hb : d112769 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12305, d112769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12305, d112769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12309 q = 1) (hb : d112773 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12309, d112773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52593 q ha hb
    | true =>
      simp only [d12309, d112773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
  have h6 (q : Pattern) (ha : d12310 q = 1) (hb : d112774 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12310, d112774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12310, d112774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12311 q = 1) (hb : d112775 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12311, d112775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12311, d112775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d112789 q = 1) (hb : d162108 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112789, d162108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52597 q ha hb
    | true =>
      simp only [d112789, d162108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52580 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d112698 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d112790 q = 1) (hb : d162109 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112790, d162109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d112790, d162109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d12345 q = 1) (hb : d112795 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12345, d112795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52594 q ha hb
    | true =>
      simp only [d12345, d112795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12346 q = 1) (hb : d112796 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12346, d112796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d12346, d112796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d112797 q = 1) (hb : d162110 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112797, d162110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d112797, d162110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d112798 q = 1) (hb : d162111 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112798, d162111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d112798, d162111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d112799 q = 1) (hb : d162112 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112799, d162112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d112799, d162112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d112800 q = 1) (hb : d162113 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112800, d162113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112800, d162113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro52599 (p : Pattern) (ha : d12351 p = 1) (hb : d112801 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d112692 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d112692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52579 q ha hb
    | true =>
      simp only [d12228, d112692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d112693 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d112693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d112693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12230 q = 1) (hb : d112694 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d112694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d112694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12231 q = 1) (hb : d112695 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12231, d112695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12231, d112695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12300 q = 1) (hb : d112764 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12300, d112764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12300, d112764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12351 q = 1) (hb : d112801 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12351, d112801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12351, d112801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro52600 (p : Pattern) (ha : d12356 p = 1) (hb : d112806 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d112692 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d112692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52579 q ha hb
    | true =>
      simp only [d12228, d112692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d112693 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d112693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d112693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12230 q = 1) (hb : d112694 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d112694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d112694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12306 q = 1) (hb : d112770 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12306, d112770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12306, d112770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12307 q = 1) (hb : d112771 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12307, d112771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12307, d112771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12356 q = 1) (hb : d112806 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12356, d112806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12356, d112806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro52601 (p : Pattern) (ha : d12365 p = 1) (hb : d112813 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d112692 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d112692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52579 q ha hb
    | true =>
      simp only [d12228, d112692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d112693 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d112693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d112693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12341 q = 1) (hb : d112791 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12341, d112791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12341, d112791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12342 q = 1) (hb : d112792 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12342, d112792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12342, d112792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12343 q = 1) (hb : d112793 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12343, d112793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12343, d112793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12365 q = 1) (hb : d112813 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12365, d112813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12365, d112813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52602 (p : Pattern) (ha : d112810 p = 1) (hb : d162114 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112783 q = 1) (hb : d162102 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112783, d162102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52596 q ha hb
    | true =>
      simp only [d112783, d162102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112784 q = 1) (hb : d162103 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112784, d162103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112784, d162103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12228 q = 1) (hb : d112692 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d112692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52579 q ha hb
    | true =>
      simp only [d12228, d112692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12229 q = 1) (hb : d112693 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d112693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d112693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112785 q = 1) (hb : d162104 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112785, d162104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112785, d162104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112786 q = 1) (hb : d162105 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112786, d162105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112786, d162105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112787 q = 1) (hb : d162106 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112787, d162106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112787, d162106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112810 q = 1) (hb : d162114 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112810, d162114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112810, d162114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52603 (p : Pattern) (ha : d112819 p = 1) (hb : d162120 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12302 q = 1) (hb : d112766 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12302, d112766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52592 q ha hb
    | true =>
      simp only [d12302, d112766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
  have h2 (q : Pattern) (ha : d12303 q = 1) (hb : d112767 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12303, d112767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12303, d112767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12304 q = 1) (hb : d112768 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12304, d112768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12304, d112768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12305 q = 1) (hb : d112769 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12305, d112769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12305, d112769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12309 q = 1) (hb : d112773 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12309, d112773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52593 q ha hb
    | true =>
      simp only [d12309, d112773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
  have h6 (q : Pattern) (ha : d12310 q = 1) (hb : d112774 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12310, d112774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12310, d112774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12311 q = 1) (hb : d112775 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12311, d112775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12311, d112775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d112789 q = 1) (hb : d162108 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112789, d162108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52597 q ha hb
    | true =>
      simp only [d112789, d162108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52580 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d112698 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d112790 q = 1) (hb : d162109 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112790, d162109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d112790, d162109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d12345 q = 1) (hb : d112795 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12345, d112795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52594 q ha hb
    | true =>
      simp only [d12345, d112795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12346 q = 1) (hb : d112796 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12346, d112796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d12346, d112796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d112797 q = 1) (hb : d162110 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112797, d162110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d112797, d162110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d112798 q = 1) (hb : d162111 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112798, d162111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d112798, d162111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d112799 q = 1) (hb : d162112 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112799, d162112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d112799, d162112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d12352 q = 1) (hb : d112802 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12352, d112802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52599 q ha hb
    | true =>
      simp only [d12352, d112802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q ha hb
  have h17 (q : Pattern) (ha : d12353 q = 1) (hb : d112803 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12353, d112803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12353, d112803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d12354 q = 1) (hb : d112804 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12354, d112804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d12354, d112804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d12355 q = 1) (hb : d112805 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12355, d112805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12355, d112805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d12357 q = 1) (hb : d112807 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12357, d112807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52600 q ha hb
    | true =>
      simp only [d12357, d112807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q ha hb
  have h21 (q : Pattern) (ha : d12358 q = 1) (hb : d112808 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12358, d112808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12358, d112808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d12359 q = 1) (hb : d112809 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12359, d112809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d12359, d112809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d112811 q = 1) (hb : d162115 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112811, d162115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52602 q ha hb
    | true =>
      simp only [d112811, d162115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52582 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d112705 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d112812 q = 1) (hb : d162116 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112812, d162116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d112812, d162116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d12366 q = 1) (hb : d112814 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12366, d112814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52601 q ha hb
    | true =>
      simp only [d12366, d112814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d12367 q = 1) (hb : d112815 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12367, d112815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d12367, d112815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d112816 q = 1) (hb : d162117 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112816, d162117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d112816, d162117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d112817 q = 1) (hb : d162118 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112817, d162118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d112817, d162118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d112818 q = 1) (hb : d162119 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112818, d162119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d112818, d162119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d112819 q = 1) (hb : d162120 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112819, d162120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d112819, d162120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro52604 (p : Pattern) (ha : d112828 p = 1) (hb : d162127 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112811 q = 1) (hb : d162115 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112811, d162115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52602 q ha hb
    | true =>
      simp only [d112811, d162115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52582 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112705 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d112812 q = 1) (hb : d162116 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112812, d162116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d112812, d162116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d12366 q = 1) (hb : d112814 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12366, d112814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52601 q ha hb
    | true =>
      simp only [d12366, d112814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12367 q = 1) (hb : d112815 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12367, d112815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12367, d112815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d112816 q = 1) (hb : d162117 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112816, d162117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112816, d162117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d112826 q = 1) (hb : d162125 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112826, d162125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112826, d162125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112827 q = 1) (hb : d162126 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112827, d162126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112827, d162126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112828 q = 1) (hb : d162127 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112828, d162127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112828, d162127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro52605 (p : Pattern) (ha : d12418 p = 1) (hb : d112852 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12262 q = 1) (hb : d112726 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12262, d112726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52585 q ha hb
    | true =>
      simp only [d12262, d112726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12263 q = 1) (hb : d112727 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12263, d112727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12263, d112727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12415 q = 1) (hb : d112849 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12415, d112849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12415, d112849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12416 q = 1) (hb : d112850 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12416, d112850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12416, d112850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12417 q = 1) (hb : d112851 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12417, d112851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12417, d112851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12418 q = 1) (hb : d112852 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12418, d112852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12418, d112852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52606 (p : Pattern) (ha : d6210 p = 1) (hb : d112834 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d412 q = 1) (hb : d52178 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d413 q = 1) (hb : d52179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d413, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d414 q = 1) (hb : d52180 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d414, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d415 q = 1) (hb : d52181 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d415, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d971 q = 1) (hb : d52044 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33341 q ha hb
  have h8 (q : Pattern) (ha : d751 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33341 q ha hb
    | true =>
      simp only [d751, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d972 q = 1) (hb : d52045 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d972, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d752 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d752, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d973 q = 1) (hb : d52046 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d973, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d974 q = 1) (hb : d52047 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d974, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d975 q = 1) (hb : d52182 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d975, d52182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d975, d52182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d6210 q = 1) (hb : d112834 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6210, d112834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d6210, d112834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro52607 (p : Pattern) (ha : d112840 p = 1) (hb : d162138 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112835 q = 1) (hb : d162133 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d112835, d162133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52606 q hb ha
    | true =>
      simp only [d112835, d162133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10860 q hb ha
  have h2 (q : Pattern) (ha : d112836 q = 1) (hb : d162134 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d112836, d162134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112836, d162134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112837 q = 1) (hb : d162135 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d112837, d162135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112837, d162135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6079 q = 1) (hb : d75841 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d75841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10860 q ha hb
    | true =>
      simp only [d6079, d75841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
  have h5 (q : Pattern) (ha : d6080 q = 1) (hb : d75842 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d75842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6080, d75842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6081 q = 1) (hb : d75843 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d75843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6081, d75843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112838 q = 1) (hb : d162136 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d112838, d162136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112838, d162136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d72 q = 1) (hb : d51924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
    | true =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d73 q = 1) (hb : d51925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12259 q = 1) (hb : d112723 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12259, d112723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12259, d112723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d112839 q = 1) (hb : d162137 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d112839, d162137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112839, d162137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d112840 q = 1) (hb : d162138 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d112840, d162138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d112840, d162138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro52608 (p : Pattern) (ha : d112846 p = 1) (hb : d162144 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112841 q = 1) (hb : d162139 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112841, d162139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52607 q ha hb
    | true =>
      simp only [d112841, d162139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112842 q = 1) (hb : d162140 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112842, d162140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112842, d162140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12262 q = 1) (hb : d112726 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12262, d112726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52585 q ha hb
    | true =>
      simp only [d12262, d112726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12263 q = 1) (hb : d112727 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12263, d112727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12263, d112727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112843 q = 1) (hb : d162141 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112843, d162141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112843, d162141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112844 q = 1) (hb : d162142 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112844, d162142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112844, d162142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112845 q = 1) (hb : d162143 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112845, d162143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112845, d162143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112846 q = 1) (hb : d162144 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112846, d162144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112846, d162144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52609 (p : Pattern) (ha : d112858 p = 1) (hb : d162150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112847 q = 1) (hb : d162145 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112847, d162145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52608 q ha hb
    | true =>
      simp only [d112847, d162145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52586 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112732 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d112848 q = 1) (hb : d162146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112848, d162146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d112848, d162146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d12419 q = 1) (hb : d112853 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12419, d112853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52605 q ha hb
    | true =>
      simp only [d12419, d112853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12420 q = 1) (hb : d112854 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12420, d112854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12420, d112854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d112855 q = 1) (hb : d162147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112855, d162147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112855, d162147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d112856 q = 1) (hb : d162148 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112856, d162148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112856, d162148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112857 q = 1) (hb : d162149 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112857, d162149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112857, d162149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112858 q = 1) (hb : d162150 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112858, d162150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112858, d162150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro52610 (p : Pattern) (ha : d112864 p = 1) (hb : d162156 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12290 q = 1) (hb : d112754 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12290, d112754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12290, d112754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52589 q ha hb
  have h2 (q : Pattern) (ha : d12291 q = 1) (hb : d112755 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12291, d112755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12291, d112755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12297 q = 1) (hb : d112761 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12297, d112761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52589 q ha hb
    | true =>
      simp only [d12297, d112761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52590 q ha hb
  have h4 (q : Pattern) (ha : d12298 q = 1) (hb : d112762 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12298, d112762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12298, d112762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12299 q = 1) (hb : d112763 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d12299, d112763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12299, d112763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112820 q = 1) (hb : d162121 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112820, d162121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52598 q ha hb
    | true =>
      simp only [d112820, d162121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52603 q ha hb
  have h7 (q : Pattern) (ha : d12374 q = 1) (hb : d112822 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12374, d112822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52591 q ha hb
    | true =>
      simp only [d12374, d112822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q ha hb
  have h8 (q : Pattern) (ha : d112823 q = 1) (hb : d162122 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112823, d162122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112823, d162122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d112824 q = 1) (hb : d162123 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d112824, d162123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d112824, d162123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d112825 q = 1) (hb : d162124 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d112825, d162124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d112825, d162124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d112829 q = 1) (hb : d162128 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112829, d162128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112829, d162128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52604 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d52173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, d52173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39 q ha hb
  have h13 (q : Pattern) (ha : d112830 q = 1) (hb : d162129 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112830, d162129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d112830, d162129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d112831 q = 1) (hb : d162130 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d112831, d162130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d112831, d162130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d112832 q = 1) (hb : d162131 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d112832, d162131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d112832, d162131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d112833 q = 1) (hb : d162132 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d112833, d162132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d112833, d162132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d112859 q = 1) (hb : d162151 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112859, d162151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112859, d162151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52609 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d52210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, d52210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40 q ha hb
  have h19 (q : Pattern) (ha : d112860 q = 1) (hb : d162152 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112860, d162152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d112860, d162152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d112861 q = 1) (hb : d162153 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d112861, d162153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d112861, d162153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d112862 q = 1) (hb : d162154 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d112862, d162154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d112862, d162154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d112863 q = 1) (hb : d162155 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d112863, d162155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d112863, d162155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d112864 q = 1) (hb : d162156 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d112864, d162156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d112864, d162156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro52611 (p : Pattern) (ha : d112870 p = 1) (hb : d162162 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d51948 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, d51948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, d51948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d51949 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, d51949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, d51949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d51950 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, d51950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, d51950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, d51951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, d51951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112744 q = 1) (hb : d115271 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d112744, d115271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112744, d115271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52588 q ha hb
  have h6 (q : Pattern) (ha : d112745 q = 1) (hb : d115272 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d112745, d115272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112745, d115272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112746 q = 1) (hb : d115273 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d112746, d115273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112746, d115273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112747 q = 1) (hb : d115274 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d112747, d115274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112747, d115274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112748 q = 1) (hb : d115275 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d112748, d115275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d112748, d115275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d112865 q = 1) (hb : d162157 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d112865, d162157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112865, d162157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52610 q ha hb
  have h11 (q : Pattern) (ha : d112866 q = 1) (hb : d162158 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d112866, d162158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112866, d162158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d112867 q = 1) (hb : d162159 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d112867, d162159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112867, d162159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d112868 q = 1) (hb : d162160 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d112868, d162160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112868, d162160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d112869 q = 1) (hb : d162161 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d112869, d162161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112869, d162161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d112870 q = 1) (hb : d162162 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d112870, d162162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d112870, d162162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro52612 (p : Pattern) (ha : d112872 p = 1) (hb : d162164 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112777 q = 1) (hb : d162096 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d112777, d162096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52595 q hb ha
    | true =>
      simp only [d112777, d162096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7917 q hb ha
  have h2 (q : Pattern) (ha : d112778 q = 1) (hb : d162097 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d112778, d162097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112778, d162097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112779 q = 1) (hb : d162098 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d112779, d162098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112779, d162098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4819 q = 1) (hb : d68915 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d68915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7917 q ha hb
    | true =>
      simp only [d4819, d68915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
  have h5 (q : Pattern) (ha : d4820 q = 1) (hb : d68916 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d68916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4820, d68916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4821 q = 1) (hb : d68917 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d68917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4821, d68917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112780 q = 1) (hb : d162099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d112780, d162099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112780, d162099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d4822 q = 1) (hb : d68918 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4822, d68918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4822, d68918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d112871 q = 1) (hb : d162163 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d112871, d162163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112871, d162163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d112872 q = 1) (hb : d162164 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d112872, d162164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d112872, d162164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro52613 (p : Pattern) (ha : d112882 p = 1) (hb : d162170 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112873 q = 1) (hb : d162165 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112873, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52612 q ha hb
    | true =>
      simp only [d112873, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112874 q = 1) (hb : d162166 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112874, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112874, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d112877 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d112877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18554 q ha hb
    | true =>
      simp only [d12443, d112877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d112878 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d112878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d112878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112879 q = 1) (hb : d162167 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112879, d162167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112879, d162167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112880 q = 1) (hb : d162168 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112880, d162168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112880, d162168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112881 q = 1) (hb : d162169 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112881, d162169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112881, d162169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112882 q = 1) (hb : d162170 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112882, d162170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112882, d162170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52614 (p : Pattern) (ha : d112892 p = 1) (hb : d162176 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112887 q = 1) (hb : d162171 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112887, d162171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52613 q ha hb
    | true =>
      simp only [d112887, d162171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18555 q hb ha
  have h2 (q : Pattern) (ha : d112888 q = 1) (hb : d162172 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112888, d162172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112888, d162172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112889 q = 1) (hb : d162173 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112889, d162173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112889, d162173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112890 q = 1) (hb : d162174 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112890, d162174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112890, d162174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112891 q = 1) (hb : d162175 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112891, d162175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112891, d162175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112892 q = 1) (hb : d162176 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112892, d162176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112892, d162176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52615 (p : Pattern) (ha : d112895 p = 1) (hb : d162179 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112873 q = 1) (hb : d162165 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112873, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52612 q ha hb
    | true =>
      simp only [d112873, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112874 q = 1) (hb : d162166 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112874, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112874, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d112877 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d112877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18554 q ha hb
    | true =>
      simp only [d12443, d112877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d112878 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d112878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d112878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112879 q = 1) (hb : d162167 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112879, d162167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112879, d162167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112880 q = 1) (hb : d162168 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112880, d162168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112880, d162168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112881 q = 1) (hb : d162169 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112881, d162169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112881, d162169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112895 q = 1) (hb : d162179 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112895, d162179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112895, d162179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52616 (p : Pattern) (ha : d112902 p = 1) (hb : d162185 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112887 q = 1) (hb : d162171 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112887, d162171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52613 q ha hb
    | true =>
      simp only [d112887, d162171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18555 q hb ha
  have h2 (q : Pattern) (ha : d112888 q = 1) (hb : d162172 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112888, d162172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112888, d162172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112889 q = 1) (hb : d162173 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112889, d162173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112889, d162173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112890 q = 1) (hb : d162174 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112890, d162174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112890, d162174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112891 q = 1) (hb : d162175 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112891, d162175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112891, d162175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112897 q = 1) (hb : d162180 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112897, d162180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52615 q ha hb
    | true =>
      simp only [d112897, d162180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18556 q hb ha
  have h7 (q : Pattern) (ha : d112898 q = 1) (hb : d162181 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112898, d162181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112898, d162181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112899 q = 1) (hb : d162182 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112899, d162182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112899, d162182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d112900 q = 1) (hb : d162183 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112900, d162183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112900, d162183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d112901 q = 1) (hb : d162184 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112901, d162184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112901, d162184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d112902 q = 1) (hb : d162185 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112902, d162185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112902, d162185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro52617 (p : Pattern) (ha : d112907 p = 1) (hb : d162190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112873 q = 1) (hb : d162165 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112873, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52612 q ha hb
    | true =>
      simp only [d112873, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112874 q = 1) (hb : d162166 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112874, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112874, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d112877 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d112877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18554 q ha hb
    | true =>
      simp only [d12443, d112877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d112878 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d112878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d112878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112879 q = 1) (hb : d162167 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112879, d162167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112879, d162167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112880 q = 1) (hb : d162168 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112880, d162168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112880, d162168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112906 q = 1) (hb : d162189 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112906, d162189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112906, d162189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112907 q = 1) (hb : d162190 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112907, d162190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112907, d162190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52618 (p : Pattern) (ha : d112916 p = 1) (hb : d162197 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112873 q = 1) (hb : d162165 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112873, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52612 q ha hb
    | true =>
      simp only [d112873, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112874 q = 1) (hb : d162166 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112874, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112874, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d112877 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d112877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18554 q ha hb
    | true =>
      simp only [d12443, d112877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d112878 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d112878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d112878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112879 q = 1) (hb : d162167 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112879, d162167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112879, d162167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112914 q = 1) (hb : d162195 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112914, d162195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112914, d162195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112915 q = 1) (hb : d162196 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112915, d162196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112915, d162196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112916 q = 1) (hb : d162197 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112916, d162197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112916, d162197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52619 (p : Pattern) (ha : d12496 p = 1) (hb : d112930 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9382 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23261 q ha hb
    | true =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9384 q = 1) (hb : d101017 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12493 q = 1) (hb : d112927 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d112927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d112927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12494 q = 1) (hb : d112928 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d112928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12494, d112928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27 q = 1) (hb : d51879 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28 q = 1) (hb : d51880 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12495 q = 1) (hb : d112929 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12495, d112929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12495, d112929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12496 q = 1) (hb : d112930 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12496, d112930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12496, d112930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro52620 (p : Pattern) (ha : d112923 p = 1) (hb : d162202 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d543 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
    | true =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d544 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d545 q = 1) (hb : d52292 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d545, d52292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d545, d52292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d546 q = 1) (hb : d52293 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d546, d52293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d546, d52293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20990 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46036 q ha hb
    | true =>
      simp only [d20990, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20991 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20991, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20992 q = 1) (hb : d52120 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d20992, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20992, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20993 q = 1) (hb : d52121 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d20993, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20993, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d52294 q = 1) (hb : d162201 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d52294, d162201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52294, d162201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d112923 q = 1) (hb : d162202 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d112923, d162202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d112923, d162202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro52621 (p : Pattern) (ha : d112936 p = 1) (hb : d162211 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112924 q = 1) (hb : d162203 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d112924, d162203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52620 q ha hb
    | true =>
      simp only [d112924, d162203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52595 q hb ha
  have h2 (q : Pattern) (ha : d112925 q = 1) (hb : d162204 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d112925, d162204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112925, d162204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112926 q = 1) (hb : d162205 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d112926, d162205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112926, d162205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d112931 q = 1) (hb : d162206 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d112931, d162206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52595 q hb ha
    | true =>
      simp only [d112931, d162206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52619 q hb ha
  have h5 (q : Pattern) (ha : d112932 q = 1) (hb : d162207 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d112932, d162207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112932, d162207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112933 q = 1) (hb : d162208 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d112933, d162208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112933, d162208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112934 q = 1) (hb : d162209 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d112934, d162209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112934, d162209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112777 q = 1) (hb : d162096 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d112777, d162096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52595 q hb ha
    | true =>
      simp only [d112777, d162096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7917 q hb ha
  have h9 (q : Pattern) (ha : d112778 q = 1) (hb : d162097 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d112778, d162097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112778, d162097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d112779 q = 1) (hb : d162098 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d112779, d162098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112779, d162098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4819 q = 1) (hb : d68915 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d68915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7917 q ha hb
    | true =>
      simp only [d4819, d68915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
  have h12 (q : Pattern) (ha : d4820 q = 1) (hb : d68916 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d68916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4820, d68916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d4821 q = 1) (hb : d68917 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d68917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4821, d68917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d112780 q = 1) (hb : d162099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d112780, d162099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d112780, d162099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d112935 q = 1) (hb : d162210 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d112935, d162210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112935, d162210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d112936 q = 1) (hb : d162211 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d112936, d162211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d112936, d162211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro52622 (p : Pattern) (ha : d112942 p = 1) (hb : d162217 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112937 q = 1) (hb : d162212 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112937, d162212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52621 q ha hb
    | true =>
      simp only [d112937, d162212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112938 q = 1) (hb : d162213 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112938, d162213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112938, d162213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112873 q = 1) (hb : d162165 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112873, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52612 q ha hb
    | true =>
      simp only [d112873, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112874 q = 1) (hb : d162166 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112874, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112874, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112939 q = 1) (hb : d162214 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112939, d162214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112939, d162214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112940 q = 1) (hb : d162215 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112940, d162215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112940, d162215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112941 q = 1) (hb : d162216 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112941, d162216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112941, d162216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112942 q = 1) (hb : d162217 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112942, d162217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112942, d162217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52623 (p : Pattern) (ha : d112948 p = 1) (hb : d162223 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112873 q = 1) (hb : d162165 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112873, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52612 q ha hb
    | true =>
      simp only [d112873, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112874 q = 1) (hb : d162166 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112874, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112874, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112945 q = 1) (hb : d162220 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112945, d162220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112945, d162220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112946 q = 1) (hb : d162221 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112946, d162221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112946, d162221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112947 q = 1) (hb : d162222 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112947, d162222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112947, d162222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112948 q = 1) (hb : d162223 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112948, d162223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112948, d162223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52624 (p : Pattern) (ha : d112954 p = 1) (hb : d162229 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112910 q = 1) (hb : d162191 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112910, d162191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52617 q ha hb
    | true =>
      simp only [d112910, d162191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18567 q hb ha
  have h2 (q : Pattern) (ha : d112911 q = 1) (hb : d162192 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112911, d162192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112911, d162192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112912 q = 1) (hb : d162193 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112912, d162193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112912, d162193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112913 q = 1) (hb : d162194 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112913, d162194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112913, d162194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112920 q = 1) (hb : d162198 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112920, d162198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52618 q ha hb
    | true =>
      simp only [d112920, d162198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18568 q hb ha
  have h6 (q : Pattern) (ha : d112921 q = 1) (hb : d162199 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112921, d162199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112921, d162199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112922 q = 1) (hb : d162200 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112922, d162200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112922, d162200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112943 q = 1) (hb : d162218 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112943, d162218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52622 q ha hb
    | true =>
      simp only [d112943, d162218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52613 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d112887 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d112944 q = 1) (hb : d162219 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112944, d162219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d112944, d162219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d112949 q = 1) (hb : d162224 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112949, d162224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52623 q ha hb
    | true =>
      simp only [d112949, d162224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d112950 q = 1) (hb : d162225 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112950, d162225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d112950, d162225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d112951 q = 1) (hb : d162226 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112951, d162226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d112951, d162226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d112952 q = 1) (hb : d162227 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112952, d162227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112952, d162227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d112953 q = 1) (hb : d162228 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112953, d162228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112953, d162228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d112954 q = 1) (hb : d162229 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112954, d162229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112954, d162229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro52625 (p : Pattern) (ha : d112955 p = 1) (hb : d162230 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112873 q = 1) (hb : d162165 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112873, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52612 q ha hb
    | true =>
      simp only [d112873, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112874 q = 1) (hb : d162166 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112874, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112874, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d112877 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d112877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18554 q ha hb
    | true =>
      simp only [d12443, d112877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d112878 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d112878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d112878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112879 q = 1) (hb : d162167 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112879, d162167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112879, d162167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112880 q = 1) (hb : d162168 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112880, d162168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112880, d162168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112906 q = 1) (hb : d162189 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112906, d162189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112906, d162189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112955 q = 1) (hb : d162230 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112955, d162230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112955, d162230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52626 (p : Pattern) (ha : d112961 p = 1) (hb : d162235 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112873 q = 1) (hb : d162165 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112873, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52612 q ha hb
    | true =>
      simp only [d112873, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112874 q = 1) (hb : d162166 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112874, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112874, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d112877 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d112877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18554 q ha hb
    | true =>
      simp only [d12443, d112877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d112878 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d112878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d112878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112879 q = 1) (hb : d162167 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112879, d162167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112879, d162167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112914 q = 1) (hb : d162195 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112914, d162195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112914, d162195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112915 q = 1) (hb : d162196 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112915, d162196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112915, d162196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112961 q = 1) (hb : d162235 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112961, d162235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112961, d162235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52627 (p : Pattern) (ha : d112966 p = 1) (hb : d162239 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112937 q = 1) (hb : d162212 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112937, d162212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52621 q ha hb
    | true =>
      simp only [d112937, d162212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112938 q = 1) (hb : d162213 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112938, d162213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112938, d162213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112873 q = 1) (hb : d162165 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112873, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52612 q ha hb
    | true =>
      simp only [d112873, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112874 q = 1) (hb : d162166 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112874, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112874, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112939 q = 1) (hb : d162214 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112939, d162214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112939, d162214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112940 q = 1) (hb : d162215 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112940, d162215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112940, d162215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112941 q = 1) (hb : d162216 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112941, d162216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112941, d162216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112966 q = 1) (hb : d162239 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112966, d162239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112966, d162239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52628 (p : Pattern) (ha : d112969 p = 1) (hb : d162242 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112873 q = 1) (hb : d162165 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112873, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52612 q ha hb
    | true =>
      simp only [d112873, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112874 q = 1) (hb : d162166 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112874, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112874, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112945 q = 1) (hb : d162220 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112945, d162220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112945, d162220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112946 q = 1) (hb : d162221 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112946, d162221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112946, d162221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112947 q = 1) (hb : d162222 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112947, d162222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112947, d162222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112969 q = 1) (hb : d162242 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112969, d162242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112969, d162242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52629 (p : Pattern) (ha : d112975 p = 1) (hb : d162248 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112910 q = 1) (hb : d162191 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112910, d162191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52617 q ha hb
    | true =>
      simp only [d112910, d162191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18567 q hb ha
  have h2 (q : Pattern) (ha : d112911 q = 1) (hb : d162192 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112911, d162192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112911, d162192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112912 q = 1) (hb : d162193 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112912, d162193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112912, d162193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112913 q = 1) (hb : d162194 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112913, d162194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112913, d162194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112920 q = 1) (hb : d162198 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112920, d162198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52618 q ha hb
    | true =>
      simp only [d112920, d162198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18568 q hb ha
  have h6 (q : Pattern) (ha : d112921 q = 1) (hb : d162199 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112921, d162199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112921, d162199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112922 q = 1) (hb : d162200 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112922, d162200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112922, d162200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112943 q = 1) (hb : d162218 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112943, d162218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52622 q ha hb
    | true =>
      simp only [d112943, d162218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52613 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d112887 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d112944 q = 1) (hb : d162219 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112944, d162219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d112944, d162219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d112949 q = 1) (hb : d162224 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112949, d162224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52623 q ha hb
    | true =>
      simp only [d112949, d162224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d112950 q = 1) (hb : d162225 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112950, d162225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d112950, d162225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d112951 q = 1) (hb : d162226 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112951, d162226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d112951, d162226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d112952 q = 1) (hb : d162227 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112952, d162227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112952, d162227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d112953 q = 1) (hb : d162228 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112953, d162228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112953, d162228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d112957 q = 1) (hb : d162231 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112957, d162231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52625 q ha hb
    | true =>
      simp only [d112957, d162231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18576 q hb ha
  have h17 (q : Pattern) (ha : d112958 q = 1) (hb : d162232 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112958, d162232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112958, d162232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d112959 q = 1) (hb : d162233 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112959, d162233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d112959, d162233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d112960 q = 1) (hb : d162234 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112960, d162234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112960, d162234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d112963 q = 1) (hb : d162236 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112963, d162236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52626 q ha hb
    | true =>
      simp only [d112963, d162236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18577 q hb ha
  have h21 (q : Pattern) (ha : d112964 q = 1) (hb : d162237 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112964, d162237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112964, d162237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d112965 q = 1) (hb : d162238 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112965, d162238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d112965, d162238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d112967 q = 1) (hb : d162240 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112967, d162240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52627 q ha hb
    | true =>
      simp only [d112967, d162240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52615 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d112897 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d112968 q = 1) (hb : d162241 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112968, d162241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d112968, d162241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d112970 q = 1) (hb : d162243 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112970, d162243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52628 q ha hb
    | true =>
      simp only [d112970, d162243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d112971 q = 1) (hb : d162244 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112971, d162244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d112971, d162244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d112972 q = 1) (hb : d162245 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112972, d162245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d112972, d162245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d112973 q = 1) (hb : d162246 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112973, d162246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d112973, d162246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d112974 q = 1) (hb : d162247 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112974, d162247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d112974, d162247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d112975 q = 1) (hb : d162248 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112975, d162248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d112975, d162248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro52630 (p : Pattern) (ha : d112982 p = 1) (hb : d162250 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112887 q = 1) (hb : d162171 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112887, d162171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52613 q ha hb
    | true =>
      simp only [d112887, d162171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18555 q hb ha
  have h2 (q : Pattern) (ha : d112888 q = 1) (hb : d162172 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112888, d162172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112888, d162172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112889 q = 1) (hb : d162173 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112889, d162173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112889, d162173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112890 q = 1) (hb : d162174 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112890, d162174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112890, d162174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112891 q = 1) (hb : d162175 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112891, d162175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112891, d162175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12569 q = 1) (hb : d112977 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12569, d112977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18555 q ha hb
    | true =>
      simp only [d12569, d112977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12570 q = 1) (hb : d112978 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12570, d112978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12570, d112978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12571 q = 1) (hb : d112979 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12571, d112979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12571, d112979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12572 q = 1) (hb : d112980 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12572, d112980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12572, d112980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12573 q = 1) (hb : d112981 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12573, d112981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12573, d112981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d112982 q = 1) (hb : d162250 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112982, d162250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112982, d162250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro52631 (p : Pattern) (ha : d112995 p = 1) (hb : d162257 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112967 q = 1) (hb : d162240 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112967, d162240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52627 q ha hb
    | true =>
      simp only [d112967, d162240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52615 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112897 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d112968 q = 1) (hb : d162241 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112968, d162241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d112968, d162241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d112970 q = 1) (hb : d162243 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112970, d162243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52628 q ha hb
    | true =>
      simp only [d112970, d162243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112971 q = 1) (hb : d162244 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112971, d162244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112971, d162244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112972 q = 1) (hb : d162245 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112972, d162245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112972, d162245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112993 q = 1) (hb : d162255 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112993, d162255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112993, d162255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112994 q = 1) (hb : d162256 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112994, d162256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112994, d162256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112995 q = 1) (hb : d162257 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112995, d162257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112995, d162257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro52632 (p : Pattern) (ha : d12604 p = 1) (hb : d113012 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12599 q = 1) (hb : d113007 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d113007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d113007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23261 q ha hb
  have h2 (q : Pattern) (ha : d9382 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23261 q ha hb
    | true =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12600 q = 1) (hb : d113008 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d113008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12600, d113008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9384 q = 1) (hb : d101017 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12601 q = 1) (hb : d113009 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d113009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12601, d113009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12602 q = 1) (hb : d113010 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d113010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12602, d113010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d66 q = 1) (hb : d51918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
  have h8 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d67 q = 1) (hb : d51919 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d68 q = 1) (hb : d51920 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12603 q = 1) (hb : d113011 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12603, d113011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12603, d113011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12604 q = 1) (hb : d113012 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12604, d113012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12604, d113012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro52633 (p : Pattern) (ha : d113003 p = 1) (hb : d162264 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d659 q = 1) (hb : d52363 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d659, d52363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d659, d52363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
  have h2 (q : Pattern) (ha : d543 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
    | true =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d660 q = 1) (hb : d52364 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d660, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d660, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d544 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d661 q = 1) (hb : d52365 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d661, d52365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d661, d52365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d662 q = 1) (hb : d52366 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d662, d52366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d662, d52366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21071 q = 1) (hb : d52178 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21071, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21071, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46036 q ha hb
  have h8 (q : Pattern) (ha : d20990 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46036 q ha hb
    | true =>
      simp only [d20990, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21072 q = 1) (hb : d52179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21072, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21072, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20991 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20991, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21073 q = 1) (hb : d52180 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21073, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21073, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21074 q = 1) (hb : d52181 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21074, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21074, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d52367 q = 1) (hb : d162263 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d52367, d162263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d52367, d162263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d113003 q = 1) (hb : d162264 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d113003, d162264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113003, d162264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro52634 (p : Pattern) (ha : d113018 p = 1) (hb : d162273 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113004 q = 1) (hb : d162265 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113004, d162265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52633 q ha hb
    | true =>
      simp only [d113004, d162265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52606 q hb ha
  have h2 (q : Pattern) (ha : d113005 q = 1) (hb : d162266 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113005, d162266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113005, d162266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113006 q = 1) (hb : d162267 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113006, d162267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113006, d162267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113013 q = 1) (hb : d162268 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113013, d162268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52606 q hb ha
    | true =>
      simp only [d113013, d162268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52632 q hb ha
  have h5 (q : Pattern) (ha : d113014 q = 1) (hb : d162269 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113014, d162269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113014, d162269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113015 q = 1) (hb : d162270 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113015, d162270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113015, d162270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113016 q = 1) (hb : d162271 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113016, d162271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113016, d162271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112835 q = 1) (hb : d162133 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d112835, d162133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52606 q hb ha
    | true =>
      simp only [d112835, d162133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10860 q hb ha
  have h9 (q : Pattern) (ha : d112836 q = 1) (hb : d162134 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d112836, d162134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112836, d162134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d112837 q = 1) (hb : d162135 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d112837, d162135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112837, d162135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6079 q = 1) (hb : d75841 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d75841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10860 q ha hb
    | true =>
      simp only [d6079, d75841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
  have h12 (q : Pattern) (ha : d6080 q = 1) (hb : d75842 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d75842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6080, d75842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6081 q = 1) (hb : d75843 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d75843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6081, d75843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d112838 q = 1) (hb : d162136 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d112838, d162136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d112838, d162136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d113017 q = 1) (hb : d162272 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113017, d162272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113017, d162272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d113018 q = 1) (hb : d162273 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113018, d162273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113018, d162273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro52635 (p : Pattern) (ha : d113022 p = 1) (hb : d162277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112835 q = 1) (hb : d162133 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d112835, d162133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52606 q hb ha
    | true =>
      simp only [d112835, d162133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10860 q hb ha
  have h2 (q : Pattern) (ha : d112836 q = 1) (hb : d162134 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d112836, d162134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112836, d162134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112837 q = 1) (hb : d162135 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d112837, d162135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112837, d162135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6079 q = 1) (hb : d75841 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d75841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10860 q ha hb
    | true =>
      simp only [d6079, d75841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
  have h5 (q : Pattern) (ha : d6080 q = 1) (hb : d75842 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d75842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6080, d75842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6081 q = 1) (hb : d75843 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d75843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6081, d75843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112838 q = 1) (hb : d162136 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d112838, d162136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112838, d162136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d6082 q = 1) (hb : d75844 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6082, d75844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6082, d75844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d113021 q = 1) (hb : d162276 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113021, d162276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113021, d162276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d113022 q = 1) (hb : d162277 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113022, d162277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113022, d162277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro52636 (p : Pattern) (ha : d113028 p = 1) (hb : d162283 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113019 q = 1) (hb : d162274 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113019, d162274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52634 q ha hb
    | true =>
      simp only [d113019, d162274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113020 q = 1) (hb : d162275 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113020, d162275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113020, d162275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113023 q = 1) (hb : d162278 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113023, d162278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52635 q ha hb
    | true =>
      simp only [d113023, d162278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113024 q = 1) (hb : d162279 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113024, d162279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113024, d162279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113025 q = 1) (hb : d162280 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113025, d162280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113025, d162280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113026 q = 1) (hb : d162281 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113026, d162281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113026, d162281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113027 q = 1) (hb : d162282 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113027, d162282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113027, d162282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113028 q = 1) (hb : d162283 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113028, d162283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113028, d162283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52637 (p : Pattern) (ha : d113036 p = 1) (hb : d162287 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113023 q = 1) (hb : d162278 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113023, d162278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52635 q ha hb
    | true =>
      simp only [d113023, d162278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113024 q = 1) (hb : d162279 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113024, d162279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113024, d162279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12623 q = 1) (hb : d113031 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12623, d113031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18559 q ha hb
    | true =>
      simp only [d12623, d113031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12624 q = 1) (hb : d113032 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12624, d113032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12624, d113032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113033 q = 1) (hb : d162284 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113033, d162284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113033, d162284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113034 q = 1) (hb : d162285 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113034, d162285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113034, d162285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113035 q = 1) (hb : d162286 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113035, d162286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113035, d162286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113036 q = 1) (hb : d162287 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113036, d162287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113036, d162287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52638 (p : Pattern) (ha : d113047 p = 1) (hb : d162293 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113023 q = 1) (hb : d162278 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113023, d162278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52635 q ha hb
    | true =>
      simp only [d113023, d162278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113024 q = 1) (hb : d162279 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113024, d162279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113024, d162279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113044 q = 1) (hb : d162290 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113044, d162290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113044, d162290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113045 q = 1) (hb : d162291 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113045, d162291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113045, d162291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113046 q = 1) (hb : d162292 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113046, d162292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113046, d162292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113047 q = 1) (hb : d162293 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113047, d162293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113047, d162293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52639 (p : Pattern) (ha : d113053 p = 1) (hb : d162299 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113037 q = 1) (hb : d162288 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113037, d162288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52636 q ha hb
    | true =>
      simp only [d113037, d162288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52637 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113042 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113043 q = 1) (hb : d162289 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113043, d162289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113043, d162289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d113048 q = 1) (hb : d162294 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113048, d162294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52638 q ha hb
    | true =>
      simp only [d113048, d162294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113049 q = 1) (hb : d162295 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113049, d162295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113049, d162295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113050 q = 1) (hb : d162296 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113050, d162296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113050, d162296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113051 q = 1) (hb : d162297 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113051, d162297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113051, d162297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113052 q = 1) (hb : d162298 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113052, d162298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113052, d162298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113053 q = 1) (hb : d162299 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113053, d162299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113053, d162299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro52640 (p : Pattern) (ha : d113066 p = 1) (hb : d162305 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112893 q = 1) (hb : d162177 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112893, d162177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112893, d162177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52614 q ha hb
  have h2 (q : Pattern) (ha : d112894 q = 1) (hb : d162178 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112894, d162178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d112894, d162178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d112903 q = 1) (hb : d162186 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112903, d162186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52614 q ha hb
    | true =>
      simp only [d112903, d162186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52616 q ha hb
  have h4 (q : Pattern) (ha : d112904 q = 1) (hb : d162187 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112904, d162187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112904, d162187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112905 q = 1) (hb : d162188 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d112905, d162188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112905, d162188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112976 q = 1) (hb : d162249 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112976, d162249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52624 q ha hb
    | true =>
      simp only [d112976, d162249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52629 q ha hb
  have h7 (q : Pattern) (ha : d112989 q = 1) (hb : d162251 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112989, d162251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52630 q ha hb
    | true =>
      simp only [d112989, d162251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18557 q hb ha
  have h8 (q : Pattern) (ha : d112990 q = 1) (hb : d162252 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112990, d162252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112990, d162252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112991 q = 1) (hb : d162253 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d112991, d162253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d112991, d162253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d112992 q = 1) (hb : d162254 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d112992, d162254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112992, d162254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d112996 q = 1) (hb : d162258 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112996, d162258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112996, d162258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52631 q ha hb
  have h12 (q : Pattern) (ha : d12590 q = 1) (hb : d112998 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12590, d112998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12590, d112998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18558 q ha hb
  have h13 (q : Pattern) (ha : d112999 q = 1) (hb : d162259 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112999, d162259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d112999, d162259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d113000 q = 1) (hb : d162260 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113000, d162260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113000, d162260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d113001 q = 1) (hb : d162261 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113001, d162261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d113001, d162261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d113002 q = 1) (hb : d162262 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113002, d162262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113002, d162262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d113054 q = 1) (hb : d162300 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113054, d162300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113054, d162300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52639 q ha hb
  have h18 (q : Pattern) (ha : d12675 q = 1) (hb : d113061 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12675, d113061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12675, d113061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18561 q ha hb
  have h19 (q : Pattern) (ha : d113062 q = 1) (hb : d162301 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113062, d162301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d113062, d162301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d113063 q = 1) (hb : d162302 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113063, d162302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d113063, d162302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d113064 q = 1) (hb : d162303 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113064, d162303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d113064, d162303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d113065 q = 1) (hb : d162304 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113065, d162304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d113065, d162304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d113066 q = 1) (hb : d162305 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d113066, d162305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d113066, d162305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro52641 (p : Pattern) (ha : d113072 p = 1) (hb : d162311 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113067 q = 1) (hb : d162306 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d113067, d162306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113067, d162306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52640 q ha hb
  have h2 (q : Pattern) (ha : d113068 q = 1) (hb : d162307 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d113068, d162307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113068, d162307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113069 q = 1) (hb : d162308 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d113069, d162308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113069, d162308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113070 q = 1) (hb : d162309 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d113070, d162309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113070, d162309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113071 q = 1) (hb : d162310 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d113071, d162310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113071, d162310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113072 q = 1) (hb : d162311 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d113072, d162311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113072, d162311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52642 (p : Pattern) (ha : d113079 p = 1) (hb : d162315 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113074 q = 1) (hb : d162203 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113074, d162203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52620 q ha hb
    | true =>
      simp only [d113074, d162203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7931 q hb ha
  have h2 (q : Pattern) (ha : d113075 q = 1) (hb : d162204 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113075, d162204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113075, d162204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113076 q = 1) (hb : d162205 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113076, d162205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113076, d162205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4914 q = 1) (hb : d69007 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4914, d69007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7931 q ha hb
    | true =>
      simp only [d4914, d69007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103 q ha hb
  have h5 (q : Pattern) (ha : d4915 q = 1) (hb : d69008 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4915, d69008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4915, d69008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4916 q = 1) (hb : d69009 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4916, d69009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4916, d69009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113077 q = 1) (hb : d162313 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113077, d162313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113077, d162313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d4917 q = 1) (hb : d69010 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4917, d69010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4917, d69010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d113078 q = 1) (hb : d162314 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113078, d162314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113078, d162314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d113079 q = 1) (hb : d162315 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113079, d162315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113079, d162315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro52643 (p : Pattern) (ha : d113089 p = 1) (hb : d162321 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113080 q = 1) (hb : d162316 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113080, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52642 q ha hb
    | true =>
      simp only [d113080, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113081 q = 1) (hb : d162317 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113081, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113081, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d113084 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d113084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18594 q ha hb
    | true =>
      simp only [d12698, d113084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d113085 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d113085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d113085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113086 q = 1) (hb : d162318 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113086, d162318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113086, d162318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113087 q = 1) (hb : d162319 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113087, d162319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113087, d162319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113088 q = 1) (hb : d162320 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113088, d162320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113088, d162320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113089 q = 1) (hb : d162321 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113089, d162321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113089, d162321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52644 (p : Pattern) (ha : d113099 p = 1) (hb : d162327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113094 q = 1) (hb : d162322 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113094, d162322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52643 q ha hb
    | true =>
      simp only [d113094, d162322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18595 q hb ha
  have h2 (q : Pattern) (ha : d113095 q = 1) (hb : d162323 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113095, d162323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113095, d162323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113096 q = 1) (hb : d162324 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113096, d162324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113096, d162324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113097 q = 1) (hb : d162325 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113097, d162325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113097, d162325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113098 q = 1) (hb : d162326 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113098, d162326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113098, d162326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113099 q = 1) (hb : d162327 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113099, d162327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113099, d162327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52645 (p : Pattern) (ha : d113102 p = 1) (hb : d162330 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113080 q = 1) (hb : d162316 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113080, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52642 q ha hb
    | true =>
      simp only [d113080, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113081 q = 1) (hb : d162317 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113081, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113081, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d113084 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d113084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18594 q ha hb
    | true =>
      simp only [d12698, d113084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d113085 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d113085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d113085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113086 q = 1) (hb : d162318 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113086, d162318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113086, d162318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113087 q = 1) (hb : d162319 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113087, d162319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113087, d162319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113088 q = 1) (hb : d162320 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113088, d162320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113088, d162320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113102 q = 1) (hb : d162330 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113102, d162330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113102, d162330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52646 (p : Pattern) (ha : d113109 p = 1) (hb : d162336 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113094 q = 1) (hb : d162322 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113094, d162322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52643 q ha hb
    | true =>
      simp only [d113094, d162322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18595 q hb ha
  have h2 (q : Pattern) (ha : d113095 q = 1) (hb : d162323 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113095, d162323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113095, d162323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113096 q = 1) (hb : d162324 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113096, d162324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113096, d162324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113097 q = 1) (hb : d162325 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113097, d162325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113097, d162325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113098 q = 1) (hb : d162326 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113098, d162326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113098, d162326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113104 q = 1) (hb : d162331 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113104, d162331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52645 q ha hb
    | true =>
      simp only [d113104, d162331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18596 q hb ha
  have h7 (q : Pattern) (ha : d113105 q = 1) (hb : d162332 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113105, d162332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113105, d162332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113106 q = 1) (hb : d162333 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113106, d162333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113106, d162333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d113107 q = 1) (hb : d162334 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113107, d162334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113107, d162334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113108 q = 1) (hb : d162335 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113108, d162335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113108, d162335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113109 q = 1) (hb : d162336 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113109, d162336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113109, d162336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro52647 (p : Pattern) (ha : d113114 p = 1) (hb : d162341 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113080 q = 1) (hb : d162316 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113080, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52642 q ha hb
    | true =>
      simp only [d113080, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113081 q = 1) (hb : d162317 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113081, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113081, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d113084 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d113084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18594 q ha hb
    | true =>
      simp only [d12698, d113084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d113085 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d113085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d113085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113086 q = 1) (hb : d162318 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113086, d162318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113086, d162318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113087 q = 1) (hb : d162319 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113087, d162319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113087, d162319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113113 q = 1) (hb : d162340 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113113, d162340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113113, d162340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113114 q = 1) (hb : d162341 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113114, d162341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113114, d162341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52648 (p : Pattern) (ha : d113123 p = 1) (hb : d162348 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113080 q = 1) (hb : d162316 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113080, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52642 q ha hb
    | true =>
      simp only [d113080, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113081 q = 1) (hb : d162317 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113081, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113081, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d113084 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d113084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18594 q ha hb
    | true =>
      simp only [d12698, d113084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d113085 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d113085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d113085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113086 q = 1) (hb : d162318 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113086, d162318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113086, d162318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113121 q = 1) (hb : d162346 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113121, d162346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113121, d162346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113122 q = 1) (hb : d162347 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113122, d162347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113122, d162347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113123 q = 1) (hb : d162348 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113123, d162348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113123, d162348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52649 (p : Pattern) (ha : d12751 p = 1) (hb : d113137 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9468 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9470 q = 1) (hb : d101085 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12748 q = 1) (hb : d113134 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, d113134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12748, d113134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12749 q = 1) (hb : d113135 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, d113135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12749, d113135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d753 q = 1) (hb : d52430 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d754 q = 1) (hb : d52431 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12750 q = 1) (hb : d113136 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12750, d113136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12750, d113136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12751 q = 1) (hb : d113137 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12751, d113137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12751, d113137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro52650 (p : Pattern) (ha : d113130 p = 1) (hb : d162353 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d834 q = 1) (hb : d52511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d834, d52511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro122 q ha hb
    | true =>
      simp only [d834, d52511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d835 q = 1) (hb : d52512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d835, d52512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d835, d52512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d836 q = 1) (hb : d52513 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d836, d52513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d836, d52513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d837 q = 1) (hb : d52514 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d837, d52514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d837, d52514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21183 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21183, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46068 q ha hb
    | true =>
      simp only [d21183, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21184 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21184, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21184, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21185 q = 1) (hb : d52292 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21185, d52292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21185, d52292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21186 q = 1) (hb : d52293 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21186, d52293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21186, d52293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d52515 q = 1) (hb : d162352 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d52515, d162352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52515, d162352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d113130 q = 1) (hb : d162353 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d113130, d162353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113130, d162353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro52651 (p : Pattern) (ha : d113143 p = 1) (hb : d162362 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113131 q = 1) (hb : d162354 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113131, d162354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52650 q ha hb
    | true =>
      simp only [d113131, d162354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52620 q ha hb
  have h2 (q : Pattern) (ha : d113132 q = 1) (hb : d162355 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113132, d162355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113132, d162355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113133 q = 1) (hb : d162356 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113133, d162356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113133, d162356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113138 q = 1) (hb : d162357 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113138, d162357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52620 q ha hb
    | true =>
      simp only [d113138, d162357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52649 q hb ha
  have h5 (q : Pattern) (ha : d113139 q = 1) (hb : d162358 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113139, d162358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113139, d162358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113140 q = 1) (hb : d162359 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113140, d162359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113140, d162359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113141 q = 1) (hb : d162360 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113141, d162360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113141, d162360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113074 q = 1) (hb : d162203 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113074, d162203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52620 q ha hb
    | true =>
      simp only [d113074, d162203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7931 q hb ha
  have h9 (q : Pattern) (ha : d113075 q = 1) (hb : d162204 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113075, d162204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113075, d162204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113076 q = 1) (hb : d162205 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113076, d162205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113076, d162205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4914 q = 1) (hb : d69007 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4914, d69007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7931 q ha hb
    | true =>
      simp only [d4914, d69007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103 q ha hb
  have h12 (q : Pattern) (ha : d4915 q = 1) (hb : d69008 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4915, d69008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4915, d69008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d4916 q = 1) (hb : d69009 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4916, d69009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4916, d69009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113077 q = 1) (hb : d162313 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113077, d162313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113077, d162313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d113142 q = 1) (hb : d162361 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113142, d162361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113142, d162361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d113143 q = 1) (hb : d162362 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113143, d162362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113143, d162362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro52652 (p : Pattern) (ha : d113149 p = 1) (hb : d162368 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113144 q = 1) (hb : d162363 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113144, d162363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52651 q ha hb
    | true =>
      simp only [d113144, d162363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113145 q = 1) (hb : d162364 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113145, d162364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113145, d162364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113080 q = 1) (hb : d162316 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113080, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52642 q ha hb
    | true =>
      simp only [d113080, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113081 q = 1) (hb : d162317 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113081, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113081, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113146 q = 1) (hb : d162365 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113146, d162365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113146, d162365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113147 q = 1) (hb : d162366 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113147, d162366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113147, d162366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113148 q = 1) (hb : d162367 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113148, d162367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113148, d162367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113149 q = 1) (hb : d162368 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113149, d162368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113149, d162368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52653 (p : Pattern) (ha : d113155 p = 1) (hb : d162374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113080 q = 1) (hb : d162316 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113080, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52642 q ha hb
    | true =>
      simp only [d113080, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113081 q = 1) (hb : d162317 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113081, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113081, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113152 q = 1) (hb : d162371 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113152, d162371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113152, d162371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113153 q = 1) (hb : d162372 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113153, d162372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113153, d162372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113154 q = 1) (hb : d162373 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113154, d162373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113154, d162373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113155 q = 1) (hb : d162374 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113155, d162374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113155, d162374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52654 (p : Pattern) (ha : d113161 p = 1) (hb : d162380 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113117 q = 1) (hb : d162342 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113117, d162342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52647 q ha hb
    | true =>
      simp only [d113117, d162342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18607 q hb ha
  have h2 (q : Pattern) (ha : d113118 q = 1) (hb : d162343 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113118, d162343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113118, d162343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113119 q = 1) (hb : d162344 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113119, d162344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113119, d162344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113120 q = 1) (hb : d162345 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113120, d162345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113120, d162345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113127 q = 1) (hb : d162349 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113127, d162349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52648 q ha hb
    | true =>
      simp only [d113127, d162349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18608 q hb ha
  have h6 (q : Pattern) (ha : d113128 q = 1) (hb : d162350 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113128, d162350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113128, d162350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113129 q = 1) (hb : d162351 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113129, d162351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113129, d162351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113150 q = 1) (hb : d162369 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113150, d162369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52652 q ha hb
    | true =>
      simp only [d113150, d162369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52643 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113094 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113151 q = 1) (hb : d162370 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113151, d162370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113151, d162370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113156 q = 1) (hb : d162375 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113156, d162375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52653 q ha hb
    | true =>
      simp only [d113156, d162375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d113157 q = 1) (hb : d162376 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113157, d162376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113157, d162376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d113158 q = 1) (hb : d162377 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113158, d162377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113158, d162377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113159 q = 1) (hb : d162378 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113159, d162378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113159, d162378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d113160 q = 1) (hb : d162379 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113160, d162379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113160, d162379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d113161 q = 1) (hb : d162380 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113161, d162380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113161, d162380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro52655 (p : Pattern) (ha : d113162 p = 1) (hb : d162381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113080 q = 1) (hb : d162316 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113080, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52642 q ha hb
    | true =>
      simp only [d113080, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113081 q = 1) (hb : d162317 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113081, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113081, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d113084 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d113084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18594 q ha hb
    | true =>
      simp only [d12698, d113084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d113085 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d113085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d113085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113086 q = 1) (hb : d162318 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113086, d162318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113086, d162318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113087 q = 1) (hb : d162319 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113087, d162319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113087, d162319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113113 q = 1) (hb : d162340 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113113, d162340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113113, d162340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113162 q = 1) (hb : d162381 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113162, d162381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113162, d162381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52656 (p : Pattern) (ha : d113168 p = 1) (hb : d162386 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113080 q = 1) (hb : d162316 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113080, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52642 q ha hb
    | true =>
      simp only [d113080, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113081 q = 1) (hb : d162317 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113081, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113081, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d113084 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d113084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18594 q ha hb
    | true =>
      simp only [d12698, d113084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d113085 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d113085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d113085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113086 q = 1) (hb : d162318 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113086, d162318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113086, d162318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113121 q = 1) (hb : d162346 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113121, d162346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113121, d162346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113122 q = 1) (hb : d162347 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113122, d162347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113122, d162347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113168 q = 1) (hb : d162386 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113168, d162386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113168, d162386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52657 (p : Pattern) (ha : d113173 p = 1) (hb : d162390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113144 q = 1) (hb : d162363 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113144, d162363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52651 q ha hb
    | true =>
      simp only [d113144, d162363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113145 q = 1) (hb : d162364 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113145, d162364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113145, d162364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113080 q = 1) (hb : d162316 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113080, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52642 q ha hb
    | true =>
      simp only [d113080, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113081 q = 1) (hb : d162317 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113081, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113081, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113146 q = 1) (hb : d162365 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113146, d162365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113146, d162365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113147 q = 1) (hb : d162366 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113147, d162366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113147, d162366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113148 q = 1) (hb : d162367 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113148, d162367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113148, d162367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113173 q = 1) (hb : d162390 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113173, d162390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113173, d162390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52658 (p : Pattern) (ha : d113176 p = 1) (hb : d162393 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113080 q = 1) (hb : d162316 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113080, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52642 q ha hb
    | true =>
      simp only [d113080, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113081 q = 1) (hb : d162317 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113081, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113081, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113152 q = 1) (hb : d162371 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113152, d162371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113152, d162371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113153 q = 1) (hb : d162372 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113153, d162372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113153, d162372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113154 q = 1) (hb : d162373 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113154, d162373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113154, d162373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113176 q = 1) (hb : d162393 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113176, d162393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113176, d162393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52659 (p : Pattern) (ha : d113182 p = 1) (hb : d162399 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113117 q = 1) (hb : d162342 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113117, d162342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52647 q ha hb
    | true =>
      simp only [d113117, d162342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18607 q hb ha
  have h2 (q : Pattern) (ha : d113118 q = 1) (hb : d162343 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113118, d162343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113118, d162343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113119 q = 1) (hb : d162344 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113119, d162344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113119, d162344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113120 q = 1) (hb : d162345 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113120, d162345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113120, d162345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113127 q = 1) (hb : d162349 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113127, d162349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52648 q ha hb
    | true =>
      simp only [d113127, d162349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18608 q hb ha
  have h6 (q : Pattern) (ha : d113128 q = 1) (hb : d162350 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113128, d162350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113128, d162350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113129 q = 1) (hb : d162351 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113129, d162351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113129, d162351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113150 q = 1) (hb : d162369 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113150, d162369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52652 q ha hb
    | true =>
      simp only [d113150, d162369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52643 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113094 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113151 q = 1) (hb : d162370 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113151, d162370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113151, d162370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113156 q = 1) (hb : d162375 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113156, d162375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52653 q ha hb
    | true =>
      simp only [d113156, d162375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d113157 q = 1) (hb : d162376 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113157, d162376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113157, d162376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d113158 q = 1) (hb : d162377 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113158, d162377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113158, d162377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113159 q = 1) (hb : d162378 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113159, d162378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113159, d162378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d113160 q = 1) (hb : d162379 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113160, d162379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113160, d162379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d113164 q = 1) (hb : d162382 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113164, d162382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52655 q ha hb
    | true =>
      simp only [d113164, d162382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18616 q hb ha
  have h17 (q : Pattern) (ha : d113165 q = 1) (hb : d162383 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113165, d162383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113165, d162383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d113166 q = 1) (hb : d162384 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113166, d162384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d113166, d162384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d113167 q = 1) (hb : d162385 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113167, d162385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113167, d162385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d113170 q = 1) (hb : d162387 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113170, d162387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52656 q ha hb
    | true =>
      simp only [d113170, d162387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18617 q hb ha
  have h21 (q : Pattern) (ha : d113171 q = 1) (hb : d162388 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113171, d162388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113171, d162388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d113172 q = 1) (hb : d162389 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113172, d162389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d113172, d162389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d113174 q = 1) (hb : d162391 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113174, d162391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52657 q ha hb
    | true =>
      simp only [d113174, d162391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52645 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d113104 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d113175 q = 1) (hb : d162392 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113175, d162392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d113175, d162392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d113177 q = 1) (hb : d162394 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113177, d162394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52658 q ha hb
    | true =>
      simp only [d113177, d162394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d113178 q = 1) (hb : d162395 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113178, d162395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d113178, d162395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d113179 q = 1) (hb : d162396 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113179, d162396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d113179, d162396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d113180 q = 1) (hb : d162397 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113180, d162397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d113180, d162397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d113181 q = 1) (hb : d162398 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113181, d162398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d113181, d162398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d113182 q = 1) (hb : d162399 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113182, d162399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113182, d162399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro52660 (p : Pattern) (ha : d113189 p = 1) (hb : d162401 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113094 q = 1) (hb : d162322 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113094, d162322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52643 q ha hb
    | true =>
      simp only [d113094, d162322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18595 q hb ha
  have h2 (q : Pattern) (ha : d113095 q = 1) (hb : d162323 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113095, d162323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113095, d162323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113096 q = 1) (hb : d162324 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113096, d162324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113096, d162324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113097 q = 1) (hb : d162325 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113097, d162325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113097, d162325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113098 q = 1) (hb : d162326 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113098, d162326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113098, d162326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12828 q = 1) (hb : d113184 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12828, d113184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18595 q ha hb
    | true =>
      simp only [d12828, d113184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12829 q = 1) (hb : d113185 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12829, d113185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12829, d113185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12830 q = 1) (hb : d113186 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12830, d113186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12830, d113186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12831 q = 1) (hb : d113187 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12831, d113187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12831, d113187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12832 q = 1) (hb : d113188 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12832, d113188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12832, d113188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113189 q = 1) (hb : d162401 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113189, d162401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113189, d162401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro52661 (p : Pattern) (ha : d113202 p = 1) (hb : d162408 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113174 q = 1) (hb : d162391 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113174, d162391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52657 q ha hb
    | true =>
      simp only [d113174, d162391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52645 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113104 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113175 q = 1) (hb : d162392 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113175, d162392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113175, d162392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d113177 q = 1) (hb : d162394 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113177, d162394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52658 q ha hb
    | true =>
      simp only [d113177, d162394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113178 q = 1) (hb : d162395 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113178, d162395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113178, d162395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113179 q = 1) (hb : d162396 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113179, d162396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113179, d162396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113200 q = 1) (hb : d162406 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113200, d162406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113200, d162406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113201 q = 1) (hb : d162407 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113201, d162407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113201, d162407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113202 q = 1) (hb : d162408 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113202, d162408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113202, d162408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro52662 (p : Pattern) (ha : d12863 p = 1) (hb : d113219 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12858 q = 1) (hb : d113214 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
  have h2 (q : Pattern) (ha : d9468 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12859 q = 1) (hb : d113215 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12859, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9470 q = 1) (hb : d101085 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12860 q = 1) (hb : d113216 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12860, d113216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12860, d113216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12861 q = 1) (hb : d113217 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12861, d113217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12861, d113217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d971 q = 1) (hb : d52590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
  have h8 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d972 q = 1) (hb : d52591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d973 q = 1) (hb : d52592 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d974 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12862 q = 1) (hb : d113218 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12862, d113218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12862, d113218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12863 q = 1) (hb : d113219 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12863, d113219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12863, d113219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro52663 (p : Pattern) (ha : d113210 p = 1) (hb : d162415 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d965 q = 1) (hb : d52584 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d965, d52584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d965, d52584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro122 q ha hb
  have h2 (q : Pattern) (ha : d834 q = 1) (hb : d52511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d834, d52511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro122 q ha hb
    | true =>
      simp only [d834, d52511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d966 q = 1) (hb : d52585 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d966, d52585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d966, d52585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d835 q = 1) (hb : d52512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d835, d52512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d835, d52512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d967 q = 1) (hb : d52586 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d967, d52586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d967, d52586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d968 q = 1) (hb : d52587 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d968, d52587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d968, d52587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21309 q = 1) (hb : d52363 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21309, d52363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21309, d52363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46068 q ha hb
  have h8 (q : Pattern) (ha : d21183 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21183, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46068 q ha hb
    | true =>
      simp only [d21183, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21310 q = 1) (hb : d52364 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21310, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21310, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21184 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21184, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21184, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21311 q = 1) (hb : d52365 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21311, d52365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21311, d52365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21312 q = 1) (hb : d52366 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21312, d52366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21312, d52366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d52588 q = 1) (hb : d162414 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d52588, d162414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d52588, d162414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d113210 q = 1) (hb : d162415 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d113210, d162415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113210, d162415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro52664 (p : Pattern) (ha : d113229 p = 1) (hb : d162425 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113211 q = 1) (hb : d162416 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113211, d162416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52663 q ha hb
    | true =>
      simp only [d113211, d162416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52633 q ha hb
  have h2 (q : Pattern) (ha : d113212 q = 1) (hb : d162417 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113212, d162417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113212, d162417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113213 q = 1) (hb : d162418 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113213, d162418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113213, d162418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113220 q = 1) (hb : d162419 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113220, d162419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52633 q ha hb
    | true =>
      simp only [d113220, d162419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52662 q hb ha
  have h5 (q : Pattern) (ha : d113221 q = 1) (hb : d162420 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113221, d162420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113221, d162420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113222 q = 1) (hb : d162421 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113222, d162421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113222, d162421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113223 q = 1) (hb : d162422 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113223, d162422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113223, d162422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113224 q = 1) (hb : d162265 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113224, d162265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52633 q ha hb
    | true =>
      simp only [d113224, d162265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10873 q hb ha
  have h9 (q : Pattern) (ha : d113225 q = 1) (hb : d162266 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113225, d162266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113225, d162266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113226 q = 1) (hb : d162267 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113226, d162267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113226, d162267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6211 q = 1) (hb : d75962 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6211, d75962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10873 q ha hb
    | true =>
      simp only [d6211, d75962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro116 q ha hb
  have h12 (q : Pattern) (ha : d6212 q = 1) (hb : d75963 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6212, d75963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6212, d75963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6213 q = 1) (hb : d75964 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6213, d75964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6213, d75964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113227 q = 1) (hb : d162423 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113227, d162423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113227, d162423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d113228 q = 1) (hb : d162424 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113228, d162424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113228, d162424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d113229 q = 1) (hb : d162425 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113229, d162425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113229, d162425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro52665 (p : Pattern) (ha : d113233 p = 1) (hb : d162429 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113224 q = 1) (hb : d162265 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113224, d162265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52633 q ha hb
    | true =>
      simp only [d113224, d162265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10873 q hb ha
  have h2 (q : Pattern) (ha : d113225 q = 1) (hb : d162266 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113225, d162266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113225, d162266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113226 q = 1) (hb : d162267 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113226, d162267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113226, d162267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6211 q = 1) (hb : d75962 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6211, d75962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10873 q ha hb
    | true =>
      simp only [d6211, d75962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro116 q ha hb
  have h5 (q : Pattern) (ha : d6212 q = 1) (hb : d75963 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6212, d75963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6212, d75963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6213 q = 1) (hb : d75964 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6213, d75964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6213, d75964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113227 q = 1) (hb : d162423 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113227, d162423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113227, d162423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d6214 q = 1) (hb : d75965 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6214, d75965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6214, d75965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d113232 q = 1) (hb : d162428 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113232, d162428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113232, d162428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d113233 q = 1) (hb : d162429 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113233, d162429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113233, d162429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro52666 (p : Pattern) (ha : d113239 p = 1) (hb : d162435 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113230 q = 1) (hb : d162426 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113230, d162426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52664 q ha hb
    | true =>
      simp only [d113230, d162426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113231 q = 1) (hb : d162427 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113231, d162427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113231, d162427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113234 q = 1) (hb : d162430 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113234, d162430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52665 q ha hb
    | true =>
      simp only [d113234, d162430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113235 q = 1) (hb : d162431 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113235, d162431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113235, d162431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113236 q = 1) (hb : d162432 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113236, d162432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113236, d162432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113237 q = 1) (hb : d162433 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113237, d162433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113237, d162433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113238 q = 1) (hb : d162434 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113238, d162434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113238, d162434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113239 q = 1) (hb : d162435 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113239, d162435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113239, d162435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52667 (p : Pattern) (ha : d113247 p = 1) (hb : d162439 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113234 q = 1) (hb : d162430 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113234, d162430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52665 q ha hb
    | true =>
      simp only [d113234, d162430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113235 q = 1) (hb : d162431 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113235, d162431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113235, d162431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12886 q = 1) (hb : d113242 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12886, d113242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18599 q ha hb
    | true =>
      simp only [d12886, d113242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12887 q = 1) (hb : d113243 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12887, d113243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12887, d113243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113244 q = 1) (hb : d162436 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113244, d162436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113244, d162436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113245 q = 1) (hb : d162437 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113245, d162437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113245, d162437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113246 q = 1) (hb : d162438 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113246, d162438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113246, d162438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113247 q = 1) (hb : d162439 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113247, d162439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113247, d162439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52668 (p : Pattern) (ha : d113258 p = 1) (hb : d162445 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113234 q = 1) (hb : d162430 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113234, d162430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52665 q ha hb
    | true =>
      simp only [d113234, d162430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113235 q = 1) (hb : d162431 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113235, d162431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113235, d162431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113255 q = 1) (hb : d162442 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113255, d162442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113255, d162442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113256 q = 1) (hb : d162443 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113256, d162443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113256, d162443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113257 q = 1) (hb : d162444 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113257, d162444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113257, d162444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113258 q = 1) (hb : d162445 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113258, d162445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113258, d162445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52669 (p : Pattern) (ha : d113264 p = 1) (hb : d162451 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113248 q = 1) (hb : d162440 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113248, d162440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52666 q ha hb
    | true =>
      simp only [d113248, d162440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52667 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113253 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113254 q = 1) (hb : d162441 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113254, d162441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113254, d162441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d113259 q = 1) (hb : d162446 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113259, d162446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52668 q ha hb
    | true =>
      simp only [d113259, d162446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113260 q = 1) (hb : d162447 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113260, d162447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113260, d162447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113261 q = 1) (hb : d162448 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113261, d162448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113261, d162448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113262 q = 1) (hb : d162449 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113262, d162449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113262, d162449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113263 q = 1) (hb : d162450 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113263, d162450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113263, d162450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113264 q = 1) (hb : d162451 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113264, d162451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113264, d162451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro52670 (p : Pattern) (ha : d113277 p = 1) (hb : d162457 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113100 q = 1) (hb : d162328 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113100, d162328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113100, d162328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52644 q ha hb
  have h2 (q : Pattern) (ha : d113101 q = 1) (hb : d162329 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113101, d162329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113101, d162329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d113110 q = 1) (hb : d162337 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113110, d162337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52644 q ha hb
    | true =>
      simp only [d113110, d162337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52646 q ha hb
  have h4 (q : Pattern) (ha : d113111 q = 1) (hb : d162338 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113111, d162338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113111, d162338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113112 q = 1) (hb : d162339 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113112, d162339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113112, d162339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113183 q = 1) (hb : d162400 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113183, d162400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52654 q ha hb
    | true =>
      simp only [d113183, d162400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52659 q ha hb
  have h7 (q : Pattern) (ha : d113196 q = 1) (hb : d162402 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113196, d162402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52660 q ha hb
    | true =>
      simp only [d113196, d162402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18597 q hb ha
  have h8 (q : Pattern) (ha : d113197 q = 1) (hb : d162403 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113197, d162403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113197, d162403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113198 q = 1) (hb : d162404 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113198, d162404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113198, d162404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d113199 q = 1) (hb : d162405 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113199, d162405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113199, d162405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113203 q = 1) (hb : d162409 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113203, d162409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113203, d162409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52661 q ha hb
  have h12 (q : Pattern) (ha : d12849 q = 1) (hb : d113205 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12849, d113205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12849, d113205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18598 q ha hb
  have h13 (q : Pattern) (ha : d113206 q = 1) (hb : d162410 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113206, d162410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113206, d162410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d113207 q = 1) (hb : d162411 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113207, d162411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113207, d162411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d113208 q = 1) (hb : d162412 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113208, d162412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d113208, d162412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d113209 q = 1) (hb : d162413 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113209, d162413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113209, d162413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d113265 q = 1) (hb : d162452 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113265, d162452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113265, d162452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52669 q ha hb
  have h18 (q : Pattern) (ha : d12942 q = 1) (hb : d113272 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12942, d113272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12942, d113272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18601 q ha hb
  have h19 (q : Pattern) (ha : d113273 q = 1) (hb : d162453 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113273, d162453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d113273, d162453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d113274 q = 1) (hb : d162454 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113274, d162454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d113274, d162454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d113275 q = 1) (hb : d162455 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113275, d162455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d113275, d162455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d113276 q = 1) (hb : d162456 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113276, d162456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d113276, d162456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d113277 q = 1) (hb : d162457 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d113277, d162457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d113277, d162457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro52671 (p : Pattern) (ha : d113283 p = 1) (hb : d162463 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113278 q = 1) (hb : d162458 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d113278, d162458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113278, d162458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52670 q ha hb
  have h2 (q : Pattern) (ha : d113279 q = 1) (hb : d162459 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d113279, d162459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113279, d162459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113280 q = 1) (hb : d162460 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d113280, d162460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113280, d162460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113281 q = 1) (hb : d162461 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d113281, d162461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113281, d162461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113282 q = 1) (hb : d162462 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d113282, d162462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113282, d162462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113283 q = 1) (hb : d162463 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d113283, d162463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113283, d162463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52672 (p : Pattern) (ha : d69099 p = 1) (hb : d162469 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1110 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro150 q ha hb
    | true =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1111 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1112 q = 1) (hb : d52693 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1112, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1112, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1113 q = 1) (hb : d52694 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1113, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1113, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21755 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21755, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33425 q ha hb
    | true =>
      simp only [d21755, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21756 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21756, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21756, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21757 q = 1) (hb : d52704 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21757, d52704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21757, d52704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21758 q = 1) (hb : d52705 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21758, d52705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21758, d52705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d52706 q = 1) (hb : d162468 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d52706, d162468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52706, d162468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d69099 q = 1) (hb : d162469 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d69099, d162469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69099, d162469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro52673 (p : Pattern) (ha : d113286 p = 1) (hb : d162467 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1100 q = 1) (hb : d52681 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro149 q ha hb
    | true =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1101 q = 1) (hb : d52682 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1102 q = 1) (hb : d52683 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1102, d52683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1102, d52683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1103 q = 1) (hb : d52684 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1103, d52684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1103, d52684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21742 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21742, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46147 q ha hb
    | true =>
      simp only [d21742, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21743 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21743, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21743, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21744 q = 1) (hb : d52693 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21744, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21744, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21745 q = 1) (hb : d52694 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21745, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21745, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d52695 q = 1) (hb : d162466 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d52695, d162466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52695, d162466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d113286 q = 1) (hb : d162467 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d113286, d162467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113286, d162467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro52674 (p : Pattern) (ha : d113297 p = 1) (hb : d162482 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113287 q = 1) (hb : d162470 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113287, d162470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52673 q ha hb
    | true =>
      simp only [d113287, d162470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52672 q ha hb
  have h2 (q : Pattern) (ha : d113288 q = 1) (hb : d162471 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113288, d162471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113288, d162471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113289 q = 1) (hb : d162472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113289, d162472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113289, d162472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69114 q = 1) (hb : d162473 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d69114, d162473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52672 q ha hb
    | true =>
      simp only [d69114, d162473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7948 q hb ha
  have h5 (q : Pattern) (ha : d69115 q = 1) (hb : d162474 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d69115, d162474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69115, d162474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69116 q = 1) (hb : d162475 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d69116, d162475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69116, d162475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113290 q = 1) (hb : d162476 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113290, d162476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113290, d162476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113292 q = 1) (hb : d162477 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113292, d162477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52672 q ha hb
    | true =>
      simp only [d113292, d162477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18634 q hb ha
  have h9 (q : Pattern) (ha : d113293 q = 1) (hb : d162478 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113293, d162478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113293, d162478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113294 q = 1) (hb : d162479 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113294, d162479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113294, d162479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113295 q = 1) (hb : d162480 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113295, d162480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113295, d162480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d113296 q = 1) (hb : d162481 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113296, d162481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113296, d162481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d113297 q = 1) (hb : d162482 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113297, d162482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d113297, d162482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro52675 (p : Pattern) (ha : d113301 p = 1) (hb : d162486 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113292 q = 1) (hb : d162477 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113292, d162477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52672 q ha hb
    | true =>
      simp only [d113292, d162477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18634 q hb ha
  have h2 (q : Pattern) (ha : d113293 q = 1) (hb : d162478 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113293, d162478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113293, d162478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113294 q = 1) (hb : d162479 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113294, d162479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113294, d162479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113295 q = 1) (hb : d162480 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113295, d162480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113295, d162480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113300 q = 1) (hb : d162485 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113300, d162485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113300, d162485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113301 q = 1) (hb : d162486 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113301, d162486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113301, d162486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52676 (p : Pattern) (ha : d113307 p = 1) (hb : d162492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113298 q = 1) (hb : d162483 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113298, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52674 q ha hb
    | true =>
      simp only [d113298, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113299 q = 1) (hb : d162484 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113299, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113299, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113302 q = 1) (hb : d162487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113302, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52675 q ha hb
    | true =>
      simp only [d113302, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113303 q = 1) (hb : d162488 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113303, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113303, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113304 q = 1) (hb : d162489 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113304, d162489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113304, d162489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113305 q = 1) (hb : d162490 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113305, d162490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113305, d162490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113306 q = 1) (hb : d162491 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113306, d162491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113306, d162491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113307 q = 1) (hb : d162492 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113307, d162492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113307, d162492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52677 (p : Pattern) (ha : d113311 p = 1) (hb : d162496 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113302 q = 1) (hb : d162487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113302, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52675 q ha hb
    | true =>
      simp only [d113302, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113303 q = 1) (hb : d162488 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113303, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113303, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113308 q = 1) (hb : d162493 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113308, d162493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113308, d162493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113309 q = 1) (hb : d162494 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113309, d162494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113309, d162494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113310 q = 1) (hb : d162495 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113310, d162495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113310, d162495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113311 q = 1) (hb : d162496 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113311, d162496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113311, d162496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52678 (p : Pattern) (ha : d113317 p = 1) (hb : d162502 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113312 q = 1) (hb : d162497 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113312, d162497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52676 q ha hb
    | true =>
      simp only [d113312, d162497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52677 q ha hb
  have h2 (q : Pattern) (ha : d113313 q = 1) (hb : d162498 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113313, d162498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113313, d162498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113314 q = 1) (hb : d162499 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113314, d162499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113314, d162499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113315 q = 1) (hb : d162500 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113315, d162500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113315, d162500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113316 q = 1) (hb : d162501 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113316, d162501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113316, d162501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113317 q = 1) (hb : d162502 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113317, d162502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113317, d162502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52679 (p : Pattern) (ha : d113320 p = 1) (hb : d162505 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113298 q = 1) (hb : d162483 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113298, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52674 q ha hb
    | true =>
      simp only [d113298, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113299 q = 1) (hb : d162484 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113299, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113299, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113302 q = 1) (hb : d162487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113302, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52675 q ha hb
    | true =>
      simp only [d113302, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113303 q = 1) (hb : d162488 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113303, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113303, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113304 q = 1) (hb : d162489 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113304, d162489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113304, d162489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113305 q = 1) (hb : d162490 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113305, d162490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113305, d162490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113306 q = 1) (hb : d162491 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113306, d162491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113306, d162491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113320 q = 1) (hb : d162505 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113320, d162505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113320, d162505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52680 (p : Pattern) (ha : d113321 p = 1) (hb : d162506 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113302 q = 1) (hb : d162487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113302, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52675 q ha hb
    | true =>
      simp only [d113302, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113303 q = 1) (hb : d162488 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113303, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113303, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113308 q = 1) (hb : d162493 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113308, d162493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113308, d162493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113309 q = 1) (hb : d162494 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113309, d162494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113309, d162494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113310 q = 1) (hb : d162495 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113310, d162495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113310, d162495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113321 q = 1) (hb : d162506 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113321, d162506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113321, d162506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52681 (p : Pattern) (ha : d113327 p = 1) (hb : d162512 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113312 q = 1) (hb : d162497 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113312, d162497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52676 q ha hb
    | true =>
      simp only [d113312, d162497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52677 q ha hb
  have h2 (q : Pattern) (ha : d113313 q = 1) (hb : d162498 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113313, d162498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113313, d162498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113314 q = 1) (hb : d162499 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113314, d162499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113314, d162499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113315 q = 1) (hb : d162500 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113315, d162500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113315, d162500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113316 q = 1) (hb : d162501 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113316, d162501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113316, d162501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113322 q = 1) (hb : d162507 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113322, d162507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52679 q ha hb
    | true =>
      simp only [d113322, d162507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52680 q ha hb
  have h7 (q : Pattern) (ha : d113323 q = 1) (hb : d162508 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113323, d162508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113323, d162508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113324 q = 1) (hb : d162509 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113324, d162509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113324, d162509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d113325 q = 1) (hb : d162510 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113325, d162510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113325, d162510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113326 q = 1) (hb : d162511 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113326, d162511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113326, d162511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113327 q = 1) (hb : d162512 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113327, d162512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113327, d162512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro52682 (p : Pattern) (ha : d113332 p = 1) (hb : d162517 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113298 q = 1) (hb : d162483 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113298, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52674 q ha hb
    | true =>
      simp only [d113298, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113299 q = 1) (hb : d162484 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113299, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113299, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113302 q = 1) (hb : d162487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113302, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52675 q ha hb
    | true =>
      simp only [d113302, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113303 q = 1) (hb : d162488 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113303, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113303, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113304 q = 1) (hb : d162489 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113304, d162489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113304, d162489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113305 q = 1) (hb : d162490 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113305, d162490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113305, d162490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113331 q = 1) (hb : d162516 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113331, d162516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113331, d162516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113332 q = 1) (hb : d162517 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113332, d162517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113332, d162517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52683 (p : Pattern) (ha : d113334 p = 1) (hb : d162519 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113302 q = 1) (hb : d162487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113302, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52675 q ha hb
    | true =>
      simp only [d113302, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113303 q = 1) (hb : d162488 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113303, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113303, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113308 q = 1) (hb : d162493 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113308, d162493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113308, d162493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113309 q = 1) (hb : d162494 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113309, d162494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113309, d162494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113333 q = 1) (hb : d162518 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113333, d162518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113333, d162518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113334 q = 1) (hb : d162519 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113334, d162519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113334, d162519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52684 (p : Pattern) (ha : d113341 p = 1) (hb : d162526 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113298 q = 1) (hb : d162483 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113298, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52674 q ha hb
    | true =>
      simp only [d113298, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113299 q = 1) (hb : d162484 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113299, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113299, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113302 q = 1) (hb : d162487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113302, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52675 q ha hb
    | true =>
      simp only [d113302, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113303 q = 1) (hb : d162488 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113303, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113303, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113304 q = 1) (hb : d162489 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113304, d162489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113304, d162489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113339 q = 1) (hb : d162524 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113339, d162524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113339, d162524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113340 q = 1) (hb : d162525 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113340, d162525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113340, d162525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113341 q = 1) (hb : d162526 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113341, d162526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113341, d162526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52685 (p : Pattern) (ha : d113344 p = 1) (hb : d162529 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113302 q = 1) (hb : d162487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113302, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52675 q ha hb
    | true =>
      simp only [d113302, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113303 q = 1) (hb : d162488 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113303, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113303, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113308 q = 1) (hb : d162493 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113308, d162493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113308, d162493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113342 q = 1) (hb : d162527 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113342, d162527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113342, d162527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113343 q = 1) (hb : d162528 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113343, d162528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113343, d162528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113344 q = 1) (hb : d162529 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113344, d162529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113344, d162529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52686 (p : Pattern) (ha : d13030 p = 1) (hb : d113360 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9814 q = 1) (hb : d101335 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9814, d101335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23317 q ha hb
    | true =>
      simp only [d9814, d101335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9816 q = 1) (hb : d101337 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9816, d101337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9816, d101337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13022 q = 1) (hb : d113352 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13022, d113352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13022, d113352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13023 q = 1) (hb : d113353 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13023, d113353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13023, d113353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13025 q = 1) (hb : d113355 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13025, d113355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29765 q ha hb
    | true =>
      simp only [d13025, d113355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13026 q = 1) (hb : d113356 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13026, d113356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13026, d113356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13027 q = 1) (hb : d113357 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13027, d113357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13027, d113357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13028 q = 1) (hb : d113358 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13028, d113358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13028, d113358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13029 q = 1) (hb : d113359 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13029, d113359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13029, d113359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13030 q = 1) (hb : d113360 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13030, d113360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13030, d113360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro52687 (p : Pattern) (ha : d113348 p = 1) (hb : d162534 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1210 q = 1) (hb : d52791 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1210, d52791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro174 q ha hb
    | true =>
      simp only [d1210, d52791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1211 q = 1) (hb : d52792 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1211, d52792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1211, d52792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1212 q = 1) (hb : d52793 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1212, d52793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1212, d52793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1213 q = 1) (hb : d52794 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1213, d52794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1213, d52794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21737 q = 1) (hb : d52681 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21737, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46151 q ha hb
    | true =>
      simp only [d21737, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21738 q = 1) (hb : d52682 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21738, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21738, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21739 q = 1) (hb : d52683 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21739, d52683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21739, d52683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21740 q = 1) (hb : d52684 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21740, d52684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21740, d52684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d52795 q = 1) (hb : d162533 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d52795, d162533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52795, d162533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d113348 q = 1) (hb : d162534 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d113348, d162534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113348, d162534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro52688 (p : Pattern) (ha : d113366 p = 1) (hb : d162543 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113349 q = 1) (hb : d162535 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113349, d162535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52687 q ha hb
    | true =>
      simp only [d113349, d162535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52673 q ha hb
  have h2 (q : Pattern) (ha : d113350 q = 1) (hb : d162536 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113350, d162536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113350, d162536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113351 q = 1) (hb : d162537 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113351, d162537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113351, d162537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113361 q = 1) (hb : d162538 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113361, d162538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52673 q ha hb
    | true =>
      simp only [d113361, d162538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52686 q hb ha
  have h5 (q : Pattern) (ha : d113362 q = 1) (hb : d162539 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113362, d162539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113362, d162539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113363 q = 1) (hb : d162540 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113363, d162540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113363, d162540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113364 q = 1) (hb : d162541 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113364, d162541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113364, d162541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113287 q = 1) (hb : d162470 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113287, d162470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52673 q ha hb
    | true =>
      simp only [d113287, d162470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52672 q ha hb
  have h9 (q : Pattern) (ha : d113288 q = 1) (hb : d162471 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113288, d162471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113288, d162471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113289 q = 1) (hb : d162472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113289, d162472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113289, d162472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69114 q = 1) (hb : d162473 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d69114, d162473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52672 q ha hb
    | true =>
      simp only [d69114, d162473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7948 q hb ha
  have h12 (q : Pattern) (ha : d69115 q = 1) (hb : d162474 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d69115, d162474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69115, d162474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d69116 q = 1) (hb : d162475 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d69116, d162475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69116, d162475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113290 q = 1) (hb : d162476 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113290, d162476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113290, d162476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d113365 q = 1) (hb : d162542 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113365, d162542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113365, d162542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d113366 q = 1) (hb : d162543 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113366, d162543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113366, d162543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro52689 (p : Pattern) (ha : d113370 p = 1) (hb : d162548 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113287 q = 1) (hb : d162470 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113287, d162470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52673 q ha hb
    | true =>
      simp only [d113287, d162470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52672 q ha hb
  have h2 (q : Pattern) (ha : d113288 q = 1) (hb : d162471 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113288, d162471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113288, d162471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113289 q = 1) (hb : d162472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113289, d162472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113289, d162472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69114 q = 1) (hb : d162473 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d69114, d162473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52672 q ha hb
    | true =>
      simp only [d69114, d162473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7948 q hb ha
  have h5 (q : Pattern) (ha : d69115 q = 1) (hb : d162474 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d69115, d162474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69115, d162474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69116 q = 1) (hb : d162475 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d69116, d162475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69116, d162475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113290 q = 1) (hb : d162476 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113290, d162476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113290, d162476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69117 q = 1) (hb : d162546 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d69117, d162546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69117, d162546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d113369 q = 1) (hb : d162547 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113369, d162547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113369, d162547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113370 q = 1) (hb : d162548 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113370, d162548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113370, d162548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro52690 (p : Pattern) (ha : d113376 p = 1) (hb : d162554 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113367 q = 1) (hb : d162544 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113367, d162544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52688 q ha hb
    | true =>
      simp only [d113367, d162544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113368 q = 1) (hb : d162545 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113368, d162545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113368, d162545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113371 q = 1) (hb : d162549 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113371, d162549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52689 q ha hb
    | true =>
      simp only [d113371, d162549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113372 q = 1) (hb : d162550 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113372, d162550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113372, d162550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113373 q = 1) (hb : d162551 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113373, d162551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113373, d162551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113374 q = 1) (hb : d162552 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113374, d162552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113374, d162552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113375 q = 1) (hb : d162553 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113375, d162553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113375, d162553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113376 q = 1) (hb : d162554 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113376, d162554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113376, d162554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52691 (p : Pattern) (ha : d113380 p = 1) (hb : d162558 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113371 q = 1) (hb : d162549 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113371, d162549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52689 q ha hb
    | true =>
      simp only [d113371, d162549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113372 q = 1) (hb : d162550 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113372, d162550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113372, d162550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113302 q = 1) (hb : d162487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113302, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52675 q ha hb
    | true =>
      simp only [d113302, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113303 q = 1) (hb : d162488 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113303, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113303, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113377 q = 1) (hb : d162555 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113377, d162555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113377, d162555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113378 q = 1) (hb : d162556 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113378, d162556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113378, d162556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113379 q = 1) (hb : d162557 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113379, d162557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113379, d162557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113380 q = 1) (hb : d162558 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113380, d162558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113380, d162558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52692 (p : Pattern) (ha : d113386 p = 1) (hb : d162564 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113298 q = 1) (hb : d162483 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113298, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52674 q ha hb
    | true =>
      simp only [d113298, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113299 q = 1) (hb : d162484 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113299, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113299, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113383 q = 1) (hb : d162561 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113383, d162561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113383, d162561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113384 q = 1) (hb : d162562 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113384, d162562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113384, d162562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113385 q = 1) (hb : d162563 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113385, d162563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113385, d162563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113386 q = 1) (hb : d162564 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113386, d162564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113386, d162564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52693 (p : Pattern) (ha : d113392 p = 1) (hb : d162570 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113335 q = 1) (hb : d162520 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113335, d162520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52682 q ha hb
    | true =>
      simp only [d113335, d162520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52683 q ha hb
  have h2 (q : Pattern) (ha : d113336 q = 1) (hb : d162521 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113336, d162521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113336, d162521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113337 q = 1) (hb : d162522 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113337, d162522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113337, d162522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113338 q = 1) (hb : d162523 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113338, d162523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113338, d162523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113345 q = 1) (hb : d162530 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113345, d162530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52684 q ha hb
    | true =>
      simp only [d113345, d162530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52685 q ha hb
  have h6 (q : Pattern) (ha : d113346 q = 1) (hb : d162531 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113346, d162531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113346, d162531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113347 q = 1) (hb : d162532 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113347, d162532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113347, d162532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113381 q = 1) (hb : d162559 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113381, d162559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52690 q ha hb
    | true =>
      simp only [d113381, d162559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52691 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113312 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113382 q = 1) (hb : d162560 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113382, d162560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113382, d162560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113387 q = 1) (hb : d162565 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113387, d162565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52692 q ha hb
    | true =>
      simp only [d113387, d162565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d113388 q = 1) (hb : d162566 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113388, d162566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113388, d162566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d113389 q = 1) (hb : d162567 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113389, d162567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113389, d162567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113390 q = 1) (hb : d162568 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113390, d162568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113390, d162568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d113391 q = 1) (hb : d162569 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113391, d162569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113391, d162569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d113392 q = 1) (hb : d162570 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113392, d162570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113392, d162570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro52694 (p : Pattern) (ha : d113393 p = 1) (hb : d162571 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113298 q = 1) (hb : d162483 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113298, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52674 q ha hb
    | true =>
      simp only [d113298, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113299 q = 1) (hb : d162484 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113299, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113299, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113302 q = 1) (hb : d162487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113302, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52675 q ha hb
    | true =>
      simp only [d113302, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113303 q = 1) (hb : d162488 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113303, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113303, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113304 q = 1) (hb : d162489 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113304, d162489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113304, d162489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113305 q = 1) (hb : d162490 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113305, d162490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113305, d162490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113331 q = 1) (hb : d162516 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113331, d162516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113331, d162516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113393 q = 1) (hb : d162571 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113393, d162571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113393, d162571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52695 (p : Pattern) (ha : d113394 p = 1) (hb : d162572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113302 q = 1) (hb : d162487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113302, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52675 q ha hb
    | true =>
      simp only [d113302, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113303 q = 1) (hb : d162488 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113303, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113303, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113308 q = 1) (hb : d162493 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113308, d162493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113308, d162493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113309 q = 1) (hb : d162494 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113309, d162494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113309, d162494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113333 q = 1) (hb : d162518 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113333, d162518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113333, d162518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113394 q = 1) (hb : d162572 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113394, d162572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113394, d162572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52696 (p : Pattern) (ha : d113399 p = 1) (hb : d162577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113298 q = 1) (hb : d162483 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113298, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52674 q ha hb
    | true =>
      simp only [d113298, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113299 q = 1) (hb : d162484 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113299, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113299, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113302 q = 1) (hb : d162487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113302, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52675 q ha hb
    | true =>
      simp only [d113302, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113303 q = 1) (hb : d162488 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113303, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113303, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113304 q = 1) (hb : d162489 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113304, d162489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113304, d162489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113339 q = 1) (hb : d162524 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113339, d162524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113339, d162524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113340 q = 1) (hb : d162525 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113340, d162525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113340, d162525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113399 q = 1) (hb : d162577 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113399, d162577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113399, d162577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52697 (p : Pattern) (ha : d113400 p = 1) (hb : d162578 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113302 q = 1) (hb : d162487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113302, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52675 q ha hb
    | true =>
      simp only [d113302, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113303 q = 1) (hb : d162488 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113303, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113303, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113308 q = 1) (hb : d162493 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113308, d162493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113308, d162493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113342 q = 1) (hb : d162527 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113342, d162527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113342, d162527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113343 q = 1) (hb : d162528 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113343, d162528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113343, d162528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113400 q = 1) (hb : d162578 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113400, d162578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113400, d162578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52698 (p : Pattern) (ha : d113404 p = 1) (hb : d162582 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113367 q = 1) (hb : d162544 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113367, d162544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52688 q ha hb
    | true =>
      simp only [d113367, d162544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113368 q = 1) (hb : d162545 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113368, d162545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113368, d162545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113371 q = 1) (hb : d162549 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113371, d162549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52689 q ha hb
    | true =>
      simp only [d113371, d162549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113372 q = 1) (hb : d162550 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113372, d162550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113372, d162550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113373 q = 1) (hb : d162551 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113373, d162551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113373, d162551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113374 q = 1) (hb : d162552 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113374, d162552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113374, d162552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113375 q = 1) (hb : d162553 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113375, d162553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113375, d162553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113404 q = 1) (hb : d162582 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113404, d162582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113404, d162582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52699 (p : Pattern) (ha : d113405 p = 1) (hb : d162583 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113371 q = 1) (hb : d162549 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113371, d162549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52689 q ha hb
    | true =>
      simp only [d113371, d162549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113372 q = 1) (hb : d162550 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113372, d162550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113372, d162550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113302 q = 1) (hb : d162487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113302, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52675 q ha hb
    | true =>
      simp only [d113302, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113303 q = 1) (hb : d162488 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113303, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113303, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113377 q = 1) (hb : d162555 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113377, d162555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113377, d162555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113378 q = 1) (hb : d162556 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113378, d162556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113378, d162556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113379 q = 1) (hb : d162557 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113379, d162557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113379, d162557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113405 q = 1) (hb : d162583 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113405, d162583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113405, d162583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52700 (p : Pattern) (ha : d113408 p = 1) (hb : d162586 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113298 q = 1) (hb : d162483 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113298, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52674 q ha hb
    | true =>
      simp only [d113298, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113299 q = 1) (hb : d162484 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113299, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113299, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113383 q = 1) (hb : d162561 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113383, d162561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113383, d162561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113384 q = 1) (hb : d162562 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113384, d162562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113384, d162562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113385 q = 1) (hb : d162563 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113385, d162563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113385, d162563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113408 q = 1) (hb : d162586 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113408, d162586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113408, d162586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52701 (p : Pattern) (ha : d113414 p = 1) (hb : d162592 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113335 q = 1) (hb : d162520 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113335, d162520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52682 q ha hb
    | true =>
      simp only [d113335, d162520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52683 q ha hb
  have h2 (q : Pattern) (ha : d113336 q = 1) (hb : d162521 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113336, d162521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113336, d162521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113337 q = 1) (hb : d162522 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113337, d162522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113337, d162522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113338 q = 1) (hb : d162523 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113338, d162523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113338, d162523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113345 q = 1) (hb : d162530 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113345, d162530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52684 q ha hb
    | true =>
      simp only [d113345, d162530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52685 q ha hb
  have h6 (q : Pattern) (ha : d113346 q = 1) (hb : d162531 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113346, d162531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113346, d162531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113347 q = 1) (hb : d162532 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113347, d162532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113347, d162532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113381 q = 1) (hb : d162559 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113381, d162559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52690 q ha hb
    | true =>
      simp only [d113381, d162559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52691 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113312 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113382 q = 1) (hb : d162560 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113382, d162560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113382, d162560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113387 q = 1) (hb : d162565 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113387, d162565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52692 q ha hb
    | true =>
      simp only [d113387, d162565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d113388 q = 1) (hb : d162566 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113388, d162566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113388, d162566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d113389 q = 1) (hb : d162567 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113389, d162567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113389, d162567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113390 q = 1) (hb : d162568 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113390, d162568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113390, d162568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d113391 q = 1) (hb : d162569 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113391, d162569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113391, d162569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d113395 q = 1) (hb : d162573 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113395, d162573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52694 q ha hb
    | true =>
      simp only [d113395, d162573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52695 q ha hb
  have h17 (q : Pattern) (ha : d113396 q = 1) (hb : d162574 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113396, d162574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113396, d162574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d113397 q = 1) (hb : d162575 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113397, d162575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d113397, d162575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d113398 q = 1) (hb : d162576 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113398, d162576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113398, d162576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d113401 q = 1) (hb : d162579 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113401, d162579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52696 q ha hb
    | true =>
      simp only [d113401, d162579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52697 q ha hb
  have h21 (q : Pattern) (ha : d113402 q = 1) (hb : d162580 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113402, d162580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113402, d162580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d113403 q = 1) (hb : d162581 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113403, d162581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d113403, d162581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d113406 q = 1) (hb : d162584 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113406, d162584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52698 q ha hb
    | true =>
      simp only [d113406, d162584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52699 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d113322 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d113407 q = 1) (hb : d162585 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113407, d162585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d113407, d162585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d113409 q = 1) (hb : d162587 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113409, d162587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52700 q ha hb
    | true =>
      simp only [d113409, d162587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d113410 q = 1) (hb : d162588 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113410, d162588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d113410, d162588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d113411 q = 1) (hb : d162589 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113411, d162589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d113411, d162589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d113412 q = 1) (hb : d162590 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113412, d162590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d113412, d162590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d113413 q = 1) (hb : d162591 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113413, d162591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d113413, d162591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d113414 q = 1) (hb : d162592 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113414, d162592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113414, d162592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro52702 (p : Pattern) (ha : d113426 p = 1) (hb : d162604 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113416 q = 1) (hb : d162594 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113416, d162594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52691 q ha hb
    | true =>
      simp only [d113416, d162594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52677 q ha hb
  have h2 (q : Pattern) (ha : d113417 q = 1) (hb : d162595 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113417, d162595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113417, d162595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113418 q = 1) (hb : d162596 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113418, d162596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113418, d162596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113419 q = 1) (hb : d162597 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113419, d162597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113419, d162597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113420 q = 1) (hb : d162598 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113420, d162598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113420, d162598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113421 q = 1) (hb : d162599 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113421, d162599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52677 q ha hb
    | true =>
      simp only [d113421, d162599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113422 q = 1) (hb : d162600 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113422, d162600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113422, d162600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113423 q = 1) (hb : d162601 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113423, d162601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113423, d162601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d113424 q = 1) (hb : d162602 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113424, d162602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113424, d162602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113425 q = 1) (hb : d162603 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113425, d162603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113425, d162603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113426 q = 1) (hb : d162604 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113426, d162604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113426, d162604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro52703 (p : Pattern) (ha : d113432 p = 1) (hb : d162610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113421 q = 1) (hb : d162599 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113421, d162599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52677 q ha hb
    | true =>
      simp only [d113421, d162599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113422 q = 1) (hb : d162600 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113422, d162600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113422, d162600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113423 q = 1) (hb : d162601 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113423, d162601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113423, d162601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113424 q = 1) (hb : d162602 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113424, d162602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113424, d162602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113425 q = 1) (hb : d162603 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113425, d162603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113425, d162603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113427 q = 1) (hb : d162605 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113427, d162605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52680 q ha hb
    | true =>
      simp only [d113427, d162605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113428 q = 1) (hb : d162606 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113428, d162606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113428, d162606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113429 q = 1) (hb : d162607 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113429, d162607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113429, d162607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d113430 q = 1) (hb : d162608 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113430, d162608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113430, d162608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113431 q = 1) (hb : d162609 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113431, d162609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113431, d162609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113432 q = 1) (hb : d162610 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113432, d162610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113432, d162610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro52704 (p : Pattern) (ha : d113439 p = 1) (hb : d162617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113406 q = 1) (hb : d162584 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113406, d162584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52698 q ha hb
    | true =>
      simp only [d113406, d162584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52699 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113322 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113407 q = 1) (hb : d162585 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113407, d162585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113407, d162585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d113409 q = 1) (hb : d162587 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113409, d162587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52700 q ha hb
    | true =>
      simp only [d113409, d162587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113410 q = 1) (hb : d162588 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113410, d162588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113410, d162588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113411 q = 1) (hb : d162589 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113411, d162589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113411, d162589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113437 q = 1) (hb : d162615 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113437, d162615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113437, d162615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113438 q = 1) (hb : d162616 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113438, d162616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113438, d162616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113439 q = 1) (hb : d162617 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113439, d162617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113439, d162617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro52705 (p : Pattern) (ha : d113441 p = 1) (hb : d162619 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113427 q = 1) (hb : d162605 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113427, d162605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52680 q ha hb
    | true =>
      simp only [d113427, d162605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113428 q = 1) (hb : d162606 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113428, d162606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113428, d162606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113429 q = 1) (hb : d162607 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113429, d162607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113429, d162607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113430 q = 1) (hb : d162608 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113430, d162608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113430, d162608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113431 q = 1) (hb : d162609 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113431, d162609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113431, d162609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113441 q = 1) (hb : d162619 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113441, d162619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113441, d162619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52706 (p : Pattern) (ha : d13169 p = 1) (hb : d113461 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13160 q = 1) (hb : d113452 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13160, d113452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13160, d113452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23317 q ha hb
  have h2 (q : Pattern) (ha : d9814 q = 1) (hb : d101335 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9814, d101335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23317 q ha hb
    | true =>
      simp only [d9814, d101335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13161 q = 1) (hb : d113453 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13161, d113453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13161, d113453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9816 q = 1) (hb : d101337 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9816, d101337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9816, d101337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13162 q = 1) (hb : d113454 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13162, d113454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13162, d113454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13163 q = 1) (hb : d113455 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13163, d113455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13163, d113455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13164 q = 1) (hb : d113456 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13164, d113456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13164, d113456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29765 q ha hb
  have h8 (q : Pattern) (ha : d13025 q = 1) (hb : d113355 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13025, d113355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29765 q ha hb
    | true =>
      simp only [d13025, d113355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13165 q = 1) (hb : d113457 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13165, d113457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13165, d113457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13026 q = 1) (hb : d113356 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13026, d113356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13026, d113356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13166 q = 1) (hb : d113458 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13166, d113458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13166, d113458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13167 q = 1) (hb : d113459 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13167, d113459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13167, d113459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d13168 q = 1) (hb : d113460 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13168, d113460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13168, d113460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13169 q = 1) (hb : d113461 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13169, d113461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13169, d113461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro52707 (p : Pattern) (ha : d76089 p = 1) (hb : d162637 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1385 q = 1) (hb : d52873 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1385, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1385, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro150 q ha hb
  have h2 (q : Pattern) (ha : d1110 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro150 q ha hb
    | true =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1386 q = 1) (hb : d52874 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1386, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1386, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1111 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1387 q = 1) (hb : d52875 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1387, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1387, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1388 q = 1) (hb : d52876 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1388, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1388, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22064 q = 1) (hb : d52879 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22064, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22064, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33425 q ha hb
  have h8 (q : Pattern) (ha : d21755 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21755, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33425 q ha hb
    | true =>
      simp only [d21755, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22065 q = 1) (hb : d52880 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22065, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22065, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21756 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21756, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21756, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22066 q = 1) (hb : d52881 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22066, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22066, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22067 q = 1) (hb : d52882 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22067, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22067, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d52883 q = 1) (hb : d162636 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d52883, d162636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d52883, d162636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d76089 q = 1) (hb : d162637 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d76089, d162637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76089, d162637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro52708 (p : Pattern) (ha : d113447 p = 1) (hb : d162626 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1376 q = 1) (hb : d52864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1376, d52864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1376, d52864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro174 q ha hb
  have h2 (q : Pattern) (ha : d1210 q = 1) (hb : d52791 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1210, d52791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro174 q ha hb
    | true =>
      simp only [d1210, d52791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1377 q = 1) (hb : d52865 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1377, d52865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1377, d52865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1211 q = 1) (hb : d52792 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1211, d52792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1211, d52792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1378 q = 1) (hb : d52866 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1378, d52866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1378, d52866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1379 q = 1) (hb : d52867 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1379, d52867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1379, d52867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22028 q = 1) (hb : d52868 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22028, d52868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22028, d52868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46151 q ha hb
  have h8 (q : Pattern) (ha : d21737 q = 1) (hb : d52681 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21737, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46151 q ha hb
    | true =>
      simp only [d21737, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22029 q = 1) (hb : d52869 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22029, d52869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22029, d52869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21738 q = 1) (hb : d52682 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21738, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21738, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22030 q = 1) (hb : d52870 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22030, d52870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22030, d52870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22031 q = 1) (hb : d52871 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22031, d52871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22031, d52871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d52872 q = 1) (hb : d162625 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d52872, d162625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d52872, d162625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d113447 q = 1) (hb : d162626 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d113447, d162626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113447, d162626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro52709 (p : Pattern) (ha : d113448 p = 1) (hb : d162628 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1380 q = 1) (hb : d52868 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1380, d52868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1380, d52868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro149 q ha hb
  have h2 (q : Pattern) (ha : d1100 q = 1) (hb : d52681 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro149 q ha hb
    | true =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1381 q = 1) (hb : d52869 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1381, d52869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1381, d52869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1101 q = 1) (hb : d52682 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1382 q = 1) (hb : d52870 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1382, d52870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1382, d52870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1383 q = 1) (hb : d52871 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1383, d52871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1383, d52871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22043 q = 1) (hb : d52873 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22043, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22043, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46147 q ha hb
  have h8 (q : Pattern) (ha : d21742 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21742, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46147 q ha hb
    | true =>
      simp only [d21742, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22044 q = 1) (hb : d52874 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22044, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22044, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21743 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21743, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21743, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22045 q = 1) (hb : d52875 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22045, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22045, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22046 q = 1) (hb : d52876 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22046, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22046, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d52877 q = 1) (hb : d162627 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d52877, d162627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d52877, d162627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d113448 q = 1) (hb : d162628 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d113448, d162628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113448, d162628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro52710 (p : Pattern) (ha : d113471 p = 1) (hb : d162646 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113449 q = 1) (hb : d162629 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113449, d162629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52708 q ha hb
    | true =>
      simp only [d113449, d162629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52709 q ha hb
  have h2 (q : Pattern) (ha : d113450 q = 1) (hb : d162630 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113450, d162630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113450, d162630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113451 q = 1) (hb : d162631 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113451, d162631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113451, d162631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113462 q = 1) (hb : d162632 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113462, d162632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52709 q ha hb
    | true =>
      simp only [d113462, d162632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52706 q hb ha
  have h5 (q : Pattern) (ha : d113463 q = 1) (hb : d162633 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113463, d162633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113463, d162633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113464 q = 1) (hb : d162634 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113464, d162634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113464, d162634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113465 q = 1) (hb : d162635 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113465, d162635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113465, d162635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113466 q = 1) (hb : d162638 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113466, d162638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52709 q ha hb
    | true =>
      simp only [d113466, d162638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52707 q ha hb
  have h9 (q : Pattern) (ha : d113467 q = 1) (hb : d162639 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113467, d162639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113467, d162639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113468 q = 1) (hb : d162640 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113468, d162640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113468, d162640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d76096 q = 1) (hb : d162641 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d76096, d162641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52707 q ha hb
    | true =>
      simp only [d76096, d162641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10887 q hb ha
  have h12 (q : Pattern) (ha : d76097 q = 1) (hb : d162642 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d76097, d162642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76097, d162642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d76098 q = 1) (hb : d162643 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d76098, d162643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76098, d162643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113469 q = 1) (hb : d162644 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113469, d162644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113469, d162644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d113470 q = 1) (hb : d162645 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113470, d162645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113470, d162645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d113471 q = 1) (hb : d162646 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113471, d162646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113471, d162646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro52711 (p : Pattern) (ha : d113475 p = 1) (hb : d162651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113466 q = 1) (hb : d162638 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113466, d162638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52709 q ha hb
    | true =>
      simp only [d113466, d162638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52707 q ha hb
  have h2 (q : Pattern) (ha : d113467 q = 1) (hb : d162639 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113467, d162639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113467, d162639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113468 q = 1) (hb : d162640 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113468, d162640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113468, d162640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76096 q = 1) (hb : d162641 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d76096, d162641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52707 q ha hb
    | true =>
      simp only [d76096, d162641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10887 q hb ha
  have h5 (q : Pattern) (ha : d76097 q = 1) (hb : d162642 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d76097, d162642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76097, d162642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76098 q = 1) (hb : d162643 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d76098, d162643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76098, d162643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113469 q = 1) (hb : d162644 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113469, d162644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113469, d162644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76099 q = 1) (hb : d162649 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d76099, d162649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76099, d162649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d113474 q = 1) (hb : d162650 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113474, d162650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113474, d162650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113475 q = 1) (hb : d162651 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113475, d162651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113475, d162651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro52712 (p : Pattern) (ha : d113481 p = 1) (hb : d162657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113472 q = 1) (hb : d162647 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113472, d162647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52710 q ha hb
    | true =>
      simp only [d113472, d162647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113473 q = 1) (hb : d162648 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113473, d162648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113473, d162648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113476 q = 1) (hb : d162652 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113476, d162652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52711 q ha hb
    | true =>
      simp only [d113476, d162652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113477 q = 1) (hb : d162653 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113477, d162653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113477, d162653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113478 q = 1) (hb : d162654 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113478, d162654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113478, d162654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113479 q = 1) (hb : d162655 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113479, d162655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113479, d162655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113480 q = 1) (hb : d162656 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113480, d162656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113480, d162656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113481 q = 1) (hb : d162657 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113481, d162657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113481, d162657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52713 (p : Pattern) (ha : d113488 p = 1) (hb : d162663 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113483 q = 1) (hb : d162658 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113483, d162658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52707 q ha hb
    | true =>
      simp only [d113483, d162658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18640 q hb ha
  have h2 (q : Pattern) (ha : d113484 q = 1) (hb : d162659 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113484, d162659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113484, d162659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113485 q = 1) (hb : d162660 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113485, d162660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113485, d162660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113486 q = 1) (hb : d162661 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113486, d162661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113486, d162661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113487 q = 1) (hb : d162662 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113487, d162662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113487, d162662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113488 q = 1) (hb : d162663 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113488, d162663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113488, d162663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52714 (p : Pattern) (ha : d113494 p = 1) (hb : d162669 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113476 q = 1) (hb : d162652 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113476, d162652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52711 q ha hb
    | true =>
      simp only [d113476, d162652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113477 q = 1) (hb : d162653 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113477, d162653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113477, d162653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113489 q = 1) (hb : d162664 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113489, d162664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52713 q ha hb
    | true =>
      simp only [d113489, d162664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113490 q = 1) (hb : d162665 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113490, d162665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113490, d162665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113491 q = 1) (hb : d162666 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113491, d162666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113491, d162666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113492 q = 1) (hb : d162667 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113492, d162667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113492, d162667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113493 q = 1) (hb : d162668 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113493, d162668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113493, d162668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113494 q = 1) (hb : d162669 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113494, d162669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113494, d162669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52715 (p : Pattern) (ha : d113497 p = 1) (hb : d162673 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113466 q = 1) (hb : d162638 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113466, d162638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52709 q ha hb
    | true =>
      simp only [d113466, d162638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52707 q ha hb
  have h2 (q : Pattern) (ha : d113467 q = 1) (hb : d162639 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113467, d162639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113467, d162639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113468 q = 1) (hb : d162640 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113468, d162640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113468, d162640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76096 q = 1) (hb : d162641 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d76096, d162641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52707 q ha hb
    | true =>
      simp only [d76096, d162641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10887 q hb ha
  have h5 (q : Pattern) (ha : d76097 q = 1) (hb : d162642 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d76097, d162642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76097, d162642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76098 q = 1) (hb : d162643 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d76098, d162643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76098, d162643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113469 q = 1) (hb : d162644 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113469, d162644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113469, d162644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113483 q = 1) (hb : d162658 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113483, d162658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52707 q ha hb
    | true =>
      simp only [d113483, d162658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18640 q hb ha
  have h9 (q : Pattern) (ha : d113484 q = 1) (hb : d162659 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113484, d162659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113484, d162659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113485 q = 1) (hb : d162660 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113485, d162660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113485, d162660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113486 q = 1) (hb : d162661 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113486, d162661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113486, d162661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d113496 q = 1) (hb : d162672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113496, d162672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113496, d162672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d113497 q = 1) (hb : d162673 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113497, d162673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d113497, d162673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro52716 (p : Pattern) (ha : d113513 p = 1) (hb : d162679 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113498 q = 1) (hb : d162674 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113498, d162674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52715 q ha hb
    | true =>
      simp only [d113498, d162674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113499 q = 1) (hb : d162675 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113499, d162675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113499, d162675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113510 q = 1) (hb : d162676 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113510, d162676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113510, d162676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113511 q = 1) (hb : d162677 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113511, d162677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113511, d162677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113512 q = 1) (hb : d162678 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113512, d162678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113512, d162678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113513 q = 1) (hb : d162679 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113513, d162679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113513, d162679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52717 (p : Pattern) (ha : d113519 p = 1) (hb : d162685 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113495 q = 1) (hb : d162670 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113495, d162670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52712 q ha hb
    | true =>
      simp only [d113495, d162670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52714 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113508 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113509 q = 1) (hb : d162671 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113509, d162671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113509, d162671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d113514 q = 1) (hb : d162680 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113514, d162680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52716 q ha hb
    | true =>
      simp only [d113514, d162680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113515 q = 1) (hb : d162681 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113515, d162681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113515, d162681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113516 q = 1) (hb : d162682 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113516, d162682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113516, d162682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113517 q = 1) (hb : d162683 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113517, d162683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113517, d162683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113518 q = 1) (hb : d162684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113518, d162684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113518, d162684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113519 q = 1) (hb : d162685 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113519, d162685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113519, d162685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro52718 (p : Pattern) (ha : d113507 p = 1) (hb : d162690 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113489 q = 1) (hb : d162664 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113489, d162664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52713 q ha hb
    | true =>
      simp only [d113489, d162664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113490 q = 1) (hb : d162665 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113490, d162665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113490, d162665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113504 q = 1) (hb : d162687 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113504, d162687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113504, d162687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113505 q = 1) (hb : d162688 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113505, d162688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113505, d162688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113506 q = 1) (hb : d162689 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113506, d162689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113506, d162689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113507 q = 1) (hb : d162690 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113507, d162690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113507, d162690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52719 (p : Pattern) (ha : d113526 p = 1) (hb : d162696 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113521 q = 1) (hb : d162691 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113521, d162691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52718 q ha hb
    | true =>
      simp only [d113521, d162691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113522 q = 1) (hb : d162692 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113522, d162692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113522, d162692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113523 q = 1) (hb : d162693 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113523, d162693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113523, d162693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113524 q = 1) (hb : d162694 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113524, d162694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113524, d162694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113525 q = 1) (hb : d162695 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113525, d162695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113525, d162695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113526 q = 1) (hb : d162696 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113526, d162696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113526, d162696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52720 (p : Pattern) (ha : d113532 p = 1) (hb : d162702 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113318 q = 1) (hb : d162503 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113318, d162503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113318, d162503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52678 q ha hb
  have h2 (q : Pattern) (ha : d113319 q = 1) (hb : d162504 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113319, d162504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113319, d162504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d113328 q = 1) (hb : d162513 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113328, d162513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52678 q ha hb
    | true =>
      simp only [d113328, d162513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52681 q ha hb
  have h4 (q : Pattern) (ha : d113329 q = 1) (hb : d162514 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113329, d162514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113329, d162514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113330 q = 1) (hb : d162515 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113330, d162515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113330, d162515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113415 q = 1) (hb : d162593 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113415, d162593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52693 q ha hb
    | true =>
      simp only [d113415, d162593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52701 q ha hb
  have h7 (q : Pattern) (ha : d113433 q = 1) (hb : d162611 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113433, d162611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52702 q ha hb
    | true =>
      simp only [d113433, d162611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52703 q ha hb
  have h8 (q : Pattern) (ha : d113434 q = 1) (hb : d162612 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113434, d162612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113434, d162612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113435 q = 1) (hb : d162613 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113435, d162613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113435, d162613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d113436 q = 1) (hb : d162614 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113436, d162614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113436, d162614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113440 q = 1) (hb : d162618 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113440, d162618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113440, d162618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52704 q ha hb
  have h12 (q : Pattern) (ha : d113442 q = 1) (hb : d162620 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113442, d162620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113442, d162620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52705 q ha hb
  have h13 (q : Pattern) (ha : d113443 q = 1) (hb : d162621 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113443, d162621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113443, d162621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113444 q = 1) (hb : d162622 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113444, d162622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113444, d162622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d113445 q = 1) (hb : d162623 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113445, d162623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d113445, d162623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d113446 q = 1) (hb : d162624 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113446, d162624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113446, d162624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d113520 q = 1) (hb : d162686 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113520, d162686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113520, d162686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52717 q ha hb
  have h18 (q : Pattern) (ha : d113527 q = 1) (hb : d162697 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113527, d162697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113527, d162697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52719 q ha hb
  have h19 (q : Pattern) (ha : d113528 q = 1) (hb : d162698 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113528, d162698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d113528, d162698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d113529 q = 1) (hb : d162699 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113529, d162699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d113529, d162699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d113530 q = 1) (hb : d162700 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113530, d162700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d113530, d162700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d113531 q = 1) (hb : d162701 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113531, d162701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d113531, d162701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d113532 q = 1) (hb : d162702 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d113532, d162702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d113532, d162702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro52721 (p : Pattern) (ha : d113538 p = 1) (hb : d162708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113533 q = 1) (hb : d162703 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d113533, d162703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113533, d162703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52720 q ha hb
  have h2 (q : Pattern) (ha : d113534 q = 1) (hb : d162704 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d113534, d162704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113534, d162704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113535 q = 1) (hb : d162705 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d113535, d162705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113535, d162705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113536 q = 1) (hb : d162706 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d113536, d162706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113536, d162706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113537 q = 1) (hb : d162707 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d113537, d162707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113537, d162707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113538 q = 1) (hb : d162708 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d113538, d162708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113538, d162708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52722 (p : Pattern) (ha : d69207 p = 1) (hb : d162715 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1570 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro208 q ha hb
    | true =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1571 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1572 q = 1) (hb : d53013 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1572, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1572, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1573 q = 1) (hb : d53014 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1573, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1573, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22233 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22233, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46205 q ha hb
    | true =>
      simp only [d22233, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22234 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22234, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22234, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22235 q = 1) (hb : d53025 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22235, d53025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22235, d53025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22236 q = 1) (hb : d53026 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22236, d53026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22236, d53026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53027 q = 1) (hb : d162714 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d53027, d162714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d53027, d162714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d69207 q = 1) (hb : d162715 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d69207, d162715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69207, d162715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro52723 (p : Pattern) (ha : d113542 p = 1) (hb : d162713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1555 q = 1) (hb : d52996 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro205 q ha hb
    | true =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1556 q = 1) (hb : d52997 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1557 q = 1) (hb : d52998 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1557, d52998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1557, d52998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1558 q = 1) (hb : d52999 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1558, d52999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1558, d52999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22220 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22220, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46207 q ha hb
    | true =>
      simp only [d22220, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22221 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22221, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22221, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22222 q = 1) (hb : d53013 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22222, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22222, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22223 q = 1) (hb : d53014 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22223, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22223, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53015 q = 1) (hb : d162712 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d53015, d162712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d53015, d162712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d113542 q = 1) (hb : d162713 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d113542, d162713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113542, d162713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro52724 (p : Pattern) (ha : d113553 p = 1) (hb : d162728 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113543 q = 1) (hb : d162716 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113543, d162716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52723 q ha hb
    | true =>
      simp only [d113543, d162716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52722 q ha hb
  have h2 (q : Pattern) (ha : d113544 q = 1) (hb : d162717 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113544, d162717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113544, d162717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113545 q = 1) (hb : d162718 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113545, d162718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113545, d162718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69227 q = 1) (hb : d162719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d69227, d162719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52722 q ha hb
    | true =>
      simp only [d69227, d162719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7965 q hb ha
  have h5 (q : Pattern) (ha : d69228 q = 1) (hb : d162720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d69228, d162720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69228, d162720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69229 q = 1) (hb : d162721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d69229, d162721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69229, d162721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113546 q = 1) (hb : d162722 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113546, d162722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113546, d162722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113548 q = 1) (hb : d162723 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113548, d162723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52722 q ha hb
    | true =>
      simp only [d113548, d162723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18682 q hb ha
  have h9 (q : Pattern) (ha : d113549 q = 1) (hb : d162724 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113549, d162724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113549, d162724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113550 q = 1) (hb : d162725 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113550, d162725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113550, d162725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113551 q = 1) (hb : d162726 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113551, d162726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113551, d162726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d113552 q = 1) (hb : d162727 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113552, d162727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113552, d162727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d113553 q = 1) (hb : d162728 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113553, d162728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d113553, d162728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro52725 (p : Pattern) (ha : d113557 p = 1) (hb : d162732 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113548 q = 1) (hb : d162723 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113548, d162723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52722 q ha hb
    | true =>
      simp only [d113548, d162723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18682 q hb ha
  have h2 (q : Pattern) (ha : d113549 q = 1) (hb : d162724 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113549, d162724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113549, d162724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113550 q = 1) (hb : d162725 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113550, d162725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113550, d162725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113551 q = 1) (hb : d162726 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113551, d162726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113551, d162726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113556 q = 1) (hb : d162731 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113556, d162731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113556, d162731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113557 q = 1) (hb : d162732 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113557, d162732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113557, d162732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52726 (p : Pattern) (ha : d113563 p = 1) (hb : d162738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113554 q = 1) (hb : d162729 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113554, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52724 q ha hb
    | true =>
      simp only [d113554, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113555 q = 1) (hb : d162730 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113555, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113555, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113558 q = 1) (hb : d162733 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113558, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52725 q ha hb
    | true =>
      simp only [d113558, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113559 q = 1) (hb : d162734 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113559, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113559, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113560 q = 1) (hb : d162735 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113560, d162735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113560, d162735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113561 q = 1) (hb : d162736 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113561, d162736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113561, d162736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113562 q = 1) (hb : d162737 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113562, d162737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113562, d162737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113563 q = 1) (hb : d162738 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113563, d162738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113563, d162738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52727 (p : Pattern) (ha : d113567 p = 1) (hb : d162742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113558 q = 1) (hb : d162733 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113558, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52725 q ha hb
    | true =>
      simp only [d113558, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113559 q = 1) (hb : d162734 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113559, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113559, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113564 q = 1) (hb : d162739 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113564, d162739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113564, d162739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113565 q = 1) (hb : d162740 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113565, d162740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113565, d162740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113566 q = 1) (hb : d162741 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113566, d162741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113566, d162741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113567 q = 1) (hb : d162742 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113567, d162742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113567, d162742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52728 (p : Pattern) (ha : d113573 p = 1) (hb : d162748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113568 q = 1) (hb : d162743 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113568, d162743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52726 q ha hb
    | true =>
      simp only [d113568, d162743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52727 q ha hb
  have h2 (q : Pattern) (ha : d113569 q = 1) (hb : d162744 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113569, d162744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113569, d162744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113570 q = 1) (hb : d162745 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113570, d162745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113570, d162745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113571 q = 1) (hb : d162746 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113571, d162746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113571, d162746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113572 q = 1) (hb : d162747 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113572, d162747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113572, d162747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113573 q = 1) (hb : d162748 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113573, d162748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113573, d162748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52729 (p : Pattern) (ha : d113576 p = 1) (hb : d162751 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113554 q = 1) (hb : d162729 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113554, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52724 q ha hb
    | true =>
      simp only [d113554, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113555 q = 1) (hb : d162730 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113555, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113555, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113558 q = 1) (hb : d162733 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113558, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52725 q ha hb
    | true =>
      simp only [d113558, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113559 q = 1) (hb : d162734 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113559, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113559, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113560 q = 1) (hb : d162735 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113560, d162735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113560, d162735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113561 q = 1) (hb : d162736 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113561, d162736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113561, d162736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113562 q = 1) (hb : d162737 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113562, d162737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113562, d162737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113576 q = 1) (hb : d162751 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113576, d162751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113576, d162751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52730 (p : Pattern) (ha : d113577 p = 1) (hb : d162752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113558 q = 1) (hb : d162733 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113558, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52725 q ha hb
    | true =>
      simp only [d113558, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113559 q = 1) (hb : d162734 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113559, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113559, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113564 q = 1) (hb : d162739 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113564, d162739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113564, d162739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113565 q = 1) (hb : d162740 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113565, d162740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113565, d162740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113566 q = 1) (hb : d162741 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113566, d162741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113566, d162741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113577 q = 1) (hb : d162752 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113577, d162752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113577, d162752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52731 (p : Pattern) (ha : d113583 p = 1) (hb : d162758 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113568 q = 1) (hb : d162743 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113568, d162743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52726 q ha hb
    | true =>
      simp only [d113568, d162743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52727 q ha hb
  have h2 (q : Pattern) (ha : d113569 q = 1) (hb : d162744 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113569, d162744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113569, d162744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113570 q = 1) (hb : d162745 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113570, d162745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113570, d162745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113571 q = 1) (hb : d162746 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113571, d162746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113571, d162746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113572 q = 1) (hb : d162747 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113572, d162747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113572, d162747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113578 q = 1) (hb : d162753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113578, d162753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52729 q ha hb
    | true =>
      simp only [d113578, d162753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52730 q ha hb
  have h7 (q : Pattern) (ha : d113579 q = 1) (hb : d162754 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113579, d162754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113579, d162754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113580 q = 1) (hb : d162755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113580, d162755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113580, d162755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d113581 q = 1) (hb : d162756 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113581, d162756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113581, d162756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113582 q = 1) (hb : d162757 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113582, d162757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113582, d162757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113583 q = 1) (hb : d162758 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113583, d162758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113583, d162758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro52732 (p : Pattern) (ha : d113588 p = 1) (hb : d162763 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113554 q = 1) (hb : d162729 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113554, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52724 q ha hb
    | true =>
      simp only [d113554, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113555 q = 1) (hb : d162730 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113555, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113555, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113558 q = 1) (hb : d162733 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113558, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52725 q ha hb
    | true =>
      simp only [d113558, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113559 q = 1) (hb : d162734 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113559, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113559, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113560 q = 1) (hb : d162735 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113560, d162735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113560, d162735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113561 q = 1) (hb : d162736 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113561, d162736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113561, d162736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113587 q = 1) (hb : d162762 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113587, d162762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113587, d162762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113588 q = 1) (hb : d162763 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113588, d162763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113588, d162763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52733 (p : Pattern) (ha : d113590 p = 1) (hb : d162765 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113558 q = 1) (hb : d162733 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113558, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52725 q ha hb
    | true =>
      simp only [d113558, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113559 q = 1) (hb : d162734 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113559, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113559, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113564 q = 1) (hb : d162739 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113564, d162739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113564, d162739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113565 q = 1) (hb : d162740 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113565, d162740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113565, d162740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113589 q = 1) (hb : d162764 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113589, d162764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113589, d162764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113590 q = 1) (hb : d162765 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113590, d162765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113590, d162765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52734 (p : Pattern) (ha : d113597 p = 1) (hb : d162772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113554 q = 1) (hb : d162729 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113554, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52724 q ha hb
    | true =>
      simp only [d113554, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113555 q = 1) (hb : d162730 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113555, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113555, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113558 q = 1) (hb : d162733 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113558, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52725 q ha hb
    | true =>
      simp only [d113558, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113559 q = 1) (hb : d162734 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113559, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113559, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113560 q = 1) (hb : d162735 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113560, d162735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113560, d162735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113595 q = 1) (hb : d162770 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113595, d162770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113595, d162770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113596 q = 1) (hb : d162771 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113596, d162771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113596, d162771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113597 q = 1) (hb : d162772 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113597, d162772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113597, d162772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52735 (p : Pattern) (ha : d113600 p = 1) (hb : d162775 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113558 q = 1) (hb : d162733 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113558, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52725 q ha hb
    | true =>
      simp only [d113558, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113559 q = 1) (hb : d162734 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113559, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113559, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113564 q = 1) (hb : d162739 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113564, d162739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113564, d162739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113598 q = 1) (hb : d162773 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113598, d162773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113598, d162773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113599 q = 1) (hb : d162774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113599, d162774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113599, d162774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113600 q = 1) (hb : d162775 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113600, d162775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113600, d162775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52736 (p : Pattern) (ha : d13356 p = 1) (hb : d113616 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10099 q = 1) (hb : d101526 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10099, d101526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23345 q ha hb
    | true =>
      simp only [d10099, d101526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10101 q = 1) (hb : d101528 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10101, d101528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10101, d101528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13348 q = 1) (hb : d113608 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13348, d113608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13348, d113608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13349 q = 1) (hb : d113609 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13349, d113609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13349, d113609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13351 q = 1) (hb : d113611 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13351, d113611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29819 q ha hb
    | true =>
      simp only [d13351, d113611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13352 q = 1) (hb : d113612 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13352, d113612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13352, d113612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13353 q = 1) (hb : d113613 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13353, d113613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13353, d113613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13354 q = 1) (hb : d113614 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13354, d113614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13354, d113614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13355 q = 1) (hb : d113615 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13355, d113615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13355, d113615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13356 q = 1) (hb : d113616 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13356, d113616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13356, d113616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro52737 (p : Pattern) (ha : d113604 p = 1) (hb : d162779 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1665 q = 1) (hb : d53106 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1665, d53106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro230 q ha hb
    | true =>
      simp only [d1665, d53106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1666 q = 1) (hb : d53107 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1666, d53107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1666, d53107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1667 q = 1) (hb : d53108 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1667, d53108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1667, d53108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1668 q = 1) (hb : d53109 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1668, d53109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1668, d53109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10036 q = 1) (hb : d52996 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10036, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46211 q ha hb
    | true =>
      simp only [d10036, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10038 q = 1) (hb : d52997 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10038, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10038, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16859 q = 1) (hb : d52998 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16859, d52998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16859, d52998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16860 q = 1) (hb : d52999 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16860, d52999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16860, d52999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16861 q = 1) (hb : d53110 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16861, d53110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16861, d53110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113604 q = 1) (hb : d162779 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d113604, d162779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d113604, d162779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro52738 (p : Pattern) (ha : d113622 p = 1) (hb : d162788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113605 q = 1) (hb : d162780 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113605, d162780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52737 q ha hb
    | true =>
      simp only [d113605, d162780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52723 q ha hb
  have h2 (q : Pattern) (ha : d113606 q = 1) (hb : d162781 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113606, d162781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113606, d162781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113607 q = 1) (hb : d162782 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113607, d162782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113607, d162782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113617 q = 1) (hb : d162783 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113617, d162783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52723 q ha hb
    | true =>
      simp only [d113617, d162783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52736 q hb ha
  have h5 (q : Pattern) (ha : d113618 q = 1) (hb : d162784 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113618, d162784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113618, d162784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113619 q = 1) (hb : d162785 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113619, d162785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113619, d162785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113620 q = 1) (hb : d162786 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113620, d162786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113620, d162786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113543 q = 1) (hb : d162716 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113543, d162716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52723 q ha hb
    | true =>
      simp only [d113543, d162716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52722 q ha hb
  have h9 (q : Pattern) (ha : d113544 q = 1) (hb : d162717 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113544, d162717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113544, d162717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113545 q = 1) (hb : d162718 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113545, d162718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113545, d162718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69227 q = 1) (hb : d162719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d69227, d162719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52722 q ha hb
    | true =>
      simp only [d69227, d162719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7965 q hb ha
  have h12 (q : Pattern) (ha : d69228 q = 1) (hb : d162720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d69228, d162720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69228, d162720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d69229 q = 1) (hb : d162721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d69229, d162721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69229, d162721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113546 q = 1) (hb : d162722 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113546, d162722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113546, d162722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d113621 q = 1) (hb : d162787 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113621, d162787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113621, d162787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d113622 q = 1) (hb : d162788 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113622, d162788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113622, d162788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro52739 (p : Pattern) (ha : d113626 p = 1) (hb : d162793 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113543 q = 1) (hb : d162716 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113543, d162716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52723 q ha hb
    | true =>
      simp only [d113543, d162716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52722 q ha hb
  have h2 (q : Pattern) (ha : d113544 q = 1) (hb : d162717 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113544, d162717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113544, d162717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113545 q = 1) (hb : d162718 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113545, d162718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113545, d162718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69227 q = 1) (hb : d162719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d69227, d162719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52722 q ha hb
    | true =>
      simp only [d69227, d162719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7965 q hb ha
  have h5 (q : Pattern) (ha : d69228 q = 1) (hb : d162720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d69228, d162720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69228, d162720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69229 q = 1) (hb : d162721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d69229, d162721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69229, d162721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113546 q = 1) (hb : d162722 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113546, d162722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113546, d162722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69230 q = 1) (hb : d162791 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d69230, d162791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69230, d162791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d113625 q = 1) (hb : d162792 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113625, d162792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113625, d162792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113626 q = 1) (hb : d162793 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113626, d162793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113626, d162793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro52740 (p : Pattern) (ha : d113632 p = 1) (hb : d162799 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113623 q = 1) (hb : d162789 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113623, d162789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52738 q ha hb
    | true =>
      simp only [d113623, d162789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113624 q = 1) (hb : d162790 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113624, d162790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113624, d162790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113627 q = 1) (hb : d162794 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113627, d162794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52739 q ha hb
    | true =>
      simp only [d113627, d162794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113628 q = 1) (hb : d162795 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113628, d162795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113628, d162795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113629 q = 1) (hb : d162796 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113629, d162796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113629, d162796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113630 q = 1) (hb : d162797 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113630, d162797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113630, d162797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113631 q = 1) (hb : d162798 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113631, d162798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113631, d162798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113632 q = 1) (hb : d162799 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113632, d162799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113632, d162799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52741 (p : Pattern) (ha : d113636 p = 1) (hb : d162803 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113627 q = 1) (hb : d162794 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113627, d162794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52739 q ha hb
    | true =>
      simp only [d113627, d162794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113628 q = 1) (hb : d162795 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113628, d162795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113628, d162795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113558 q = 1) (hb : d162733 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113558, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52725 q ha hb
    | true =>
      simp only [d113558, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113559 q = 1) (hb : d162734 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113559, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113559, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113633 q = 1) (hb : d162800 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113633, d162800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113633, d162800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113634 q = 1) (hb : d162801 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113634, d162801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113634, d162801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113635 q = 1) (hb : d162802 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113635, d162802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113635, d162802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113636 q = 1) (hb : d162803 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113636, d162803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113636, d162803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52742 (p : Pattern) (ha : d113642 p = 1) (hb : d162809 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113554 q = 1) (hb : d162729 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113554, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52724 q ha hb
    | true =>
      simp only [d113554, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113555 q = 1) (hb : d162730 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113555, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113555, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113639 q = 1) (hb : d162806 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113639, d162806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113639, d162806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113640 q = 1) (hb : d162807 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113640, d162807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113640, d162807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113641 q = 1) (hb : d162808 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113641, d162808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113641, d162808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113642 q = 1) (hb : d162809 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113642, d162809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113642, d162809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52743 (p : Pattern) (ha : d113648 p = 1) (hb : d162815 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113591 q = 1) (hb : d162766 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113591, d162766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52732 q ha hb
    | true =>
      simp only [d113591, d162766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52733 q ha hb
  have h2 (q : Pattern) (ha : d113592 q = 1) (hb : d162767 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113592, d162767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113592, d162767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113593 q = 1) (hb : d162768 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113593, d162768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113593, d162768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113594 q = 1) (hb : d162769 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113594, d162769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113594, d162769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113601 q = 1) (hb : d162776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113601, d162776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52734 q ha hb
    | true =>
      simp only [d113601, d162776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52735 q ha hb
  have h6 (q : Pattern) (ha : d113602 q = 1) (hb : d162777 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113602, d162777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113602, d162777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113603 q = 1) (hb : d162778 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113603, d162778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113603, d162778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113637 q = 1) (hb : d162804 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113637, d162804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52740 q ha hb
    | true =>
      simp only [d113637, d162804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52741 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113568 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113638 q = 1) (hb : d162805 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113638, d162805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113638, d162805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113643 q = 1) (hb : d162810 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113643, d162810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52742 q ha hb
    | true =>
      simp only [d113643, d162810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d113644 q = 1) (hb : d162811 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113644, d162811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113644, d162811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d113645 q = 1) (hb : d162812 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113645, d162812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113645, d162812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113646 q = 1) (hb : d162813 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113646, d162813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113646, d162813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d113647 q = 1) (hb : d162814 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113647, d162814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113647, d162814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d113648 q = 1) (hb : d162815 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113648, d162815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113648, d162815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro52744 (p : Pattern) (ha : d113649 p = 1) (hb : d162816 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113554 q = 1) (hb : d162729 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113554, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52724 q ha hb
    | true =>
      simp only [d113554, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113555 q = 1) (hb : d162730 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113555, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113555, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113558 q = 1) (hb : d162733 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113558, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52725 q ha hb
    | true =>
      simp only [d113558, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113559 q = 1) (hb : d162734 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113559, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113559, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113560 q = 1) (hb : d162735 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113560, d162735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113560, d162735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113561 q = 1) (hb : d162736 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113561, d162736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113561, d162736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113587 q = 1) (hb : d162762 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113587, d162762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113587, d162762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113649 q = 1) (hb : d162816 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113649, d162816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113649, d162816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52745 (p : Pattern) (ha : d113650 p = 1) (hb : d162817 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113558 q = 1) (hb : d162733 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113558, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52725 q ha hb
    | true =>
      simp only [d113558, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113559 q = 1) (hb : d162734 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113559, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113559, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113564 q = 1) (hb : d162739 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113564, d162739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113564, d162739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113565 q = 1) (hb : d162740 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113565, d162740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113565, d162740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113589 q = 1) (hb : d162764 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113589, d162764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113589, d162764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113650 q = 1) (hb : d162817 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113650, d162817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113650, d162817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52746 (p : Pattern) (ha : d113655 p = 1) (hb : d162822 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113554 q = 1) (hb : d162729 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113554, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52724 q ha hb
    | true =>
      simp only [d113554, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113555 q = 1) (hb : d162730 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113555, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113555, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113558 q = 1) (hb : d162733 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113558, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52725 q ha hb
    | true =>
      simp only [d113558, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113559 q = 1) (hb : d162734 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113559, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113559, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113560 q = 1) (hb : d162735 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113560, d162735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113560, d162735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113595 q = 1) (hb : d162770 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113595, d162770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113595, d162770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113596 q = 1) (hb : d162771 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113596, d162771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113596, d162771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113655 q = 1) (hb : d162822 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113655, d162822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113655, d162822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52747 (p : Pattern) (ha : d113656 p = 1) (hb : d162823 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113558 q = 1) (hb : d162733 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113558, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52725 q ha hb
    | true =>
      simp only [d113558, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113559 q = 1) (hb : d162734 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113559, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113559, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113564 q = 1) (hb : d162739 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113564, d162739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113564, d162739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113598 q = 1) (hb : d162773 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113598, d162773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113598, d162773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113599 q = 1) (hb : d162774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113599, d162774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113599, d162774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113656 q = 1) (hb : d162823 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113656, d162823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113656, d162823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52748 (p : Pattern) (ha : d113660 p = 1) (hb : d162827 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113623 q = 1) (hb : d162789 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113623, d162789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52738 q ha hb
    | true =>
      simp only [d113623, d162789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113624 q = 1) (hb : d162790 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113624, d162790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113624, d162790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113627 q = 1) (hb : d162794 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113627, d162794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52739 q ha hb
    | true =>
      simp only [d113627, d162794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113628 q = 1) (hb : d162795 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113628, d162795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113628, d162795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113629 q = 1) (hb : d162796 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113629, d162796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113629, d162796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113630 q = 1) (hb : d162797 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113630, d162797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113630, d162797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113631 q = 1) (hb : d162798 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113631, d162798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113631, d162798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113660 q = 1) (hb : d162827 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113660, d162827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113660, d162827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52749 (p : Pattern) (ha : d113661 p = 1) (hb : d162828 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113627 q = 1) (hb : d162794 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113627, d162794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52739 q ha hb
    | true =>
      simp only [d113627, d162794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113628 q = 1) (hb : d162795 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113628, d162795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113628, d162795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113558 q = 1) (hb : d162733 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113558, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52725 q ha hb
    | true =>
      simp only [d113558, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113559 q = 1) (hb : d162734 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113559, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113559, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113633 q = 1) (hb : d162800 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113633, d162800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113633, d162800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113634 q = 1) (hb : d162801 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113634, d162801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113634, d162801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113635 q = 1) (hb : d162802 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113635, d162802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113635, d162802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113661 q = 1) (hb : d162828 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113661, d162828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113661, d162828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
end NetHack.Soko22Hazard87
