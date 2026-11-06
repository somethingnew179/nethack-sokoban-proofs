import NetHack.Soko22Hazard87.EqIntroBlocks0027
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro7000 (p : Pattern) (selected : d102919 p = 0) : d103744 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d102914 q = 0) : d103739 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d102914, d103739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6999 q selected
    | true =>
      simp only [d102914, d103739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d102915 q = 0) : d103740 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d102915, d103740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102915, d103740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d102916 q = 0) : d103741 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d102916, d103741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d102916, d103741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d102917 q = 0) : d103742 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d102917, d103742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d102917, d103742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d102918 q = 0) : d103743 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d102918, d103743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d102918, d103743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d102919 q = 0) : d103744 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d102919, d103744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102919, d103744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7001 (p : Pattern) (selected : d102925 p = 0) : d103750 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d102892 q = 0) : d103722 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d102892, d103722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6995 q selected
    | true =>
      simp only [d102892, d103722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d102893 q = 0) : d103723 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d102893, d103723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102893, d103723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d102894 q = 0) : d103724 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d102894, d103724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d102894, d103724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d102895 q = 0) : d103725 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102895, d103725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102895, d103725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d102899 q = 0) : d103729 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d102899, d103729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6996 q selected
    | true =>
      simp only [d102899, d103729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d102900 q = 0) : d103730 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d102900, d103730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102900, d103730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d102901 q = 0) : d103731 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d102901, d103731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d102901, d103731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d102906 q = 0) : d103736 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d102906, d103736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6997 q selected
    | true =>
      simp only [d102906, d103736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6991 q selected
  have h9 (q : Pattern) (selected : d102911 q = 0) : d103702 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d102911, d103702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6998 q selected
    | true =>
      simp only [d102911, d103702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d102912 q = 0) : d103737 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d102912, d103737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d102912, d103737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d102920 q = 0) : d103745 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d102920, d103745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7000 q selected
    | true =>
      simp only [d102920, d103745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d102921 q = 0) : d103746 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d102921, d103746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d102921, d103746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d102922 q = 0) : d103747 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d102922, d103747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d102922, d103747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d102923 q = 0) : d103748 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102923, d103748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d102923, d103748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d102924 q = 0) : d103749 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d102924, d103749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d102924, d103749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d102925 q = 0) : d103750 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d102925, d103750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102925, d103750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro7002 (p : Pattern) (selected : d102926 p = 0) : d103751 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78155 q = 0) : d79072 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78155, d79072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3955 q selected
    | true =>
      simp only [d78155, d79072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78156 q = 0) : d79073 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78156, d79073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78156, d79073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d102868 q = 0) : d103698 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d102868, d103698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d102868, d103698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d102869 q = 0) : d103699 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d102869, d103699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d102869, d103699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d102890 q = 0) : d103720 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d102890, d103720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102890, d103720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d102926 q = 0) : d103751 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d102926, d103751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d102926, d103751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7003 (p : Pattern) (selected : d102931 p = 0) : d103756 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78155 q = 0) : d79072 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78155, d79072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3955 q selected
    | true =>
      simp only [d78155, d79072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78156 q = 0) : d79073 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78156, d79073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78156, d79073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d102868 q = 0) : d103698 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d102868, d103698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d102868, d103698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d102896 q = 0) : d103726 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d102896, d103726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102896, d103726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d102897 q = 0) : d103727 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d102897, d103727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d102897, d103727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d102931 q = 0) : d103756 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d102931, d103756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d102931, d103756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7004 (p : Pattern) (selected : d102935 p = 0) : d103760 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78191 q = 0) : d79108 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78191, d79108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3962 q selected
    | true =>
      simp only [d78191, d79108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78192 q = 0) : d79109 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78192, d79109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78192, d79109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d78155 q = 0) : d79072 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78155, d79072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3955 q selected
    | true =>
      simp only [d78155, d79072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d78156 q = 0) : d79073 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78156, d79073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78156, d79073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d102902 q = 0) : d103732 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d102902, d103732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d102902, d103732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d102903 q = 0) : d103733 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d102903, d103733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d102903, d103733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d102904 q = 0) : d103734 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d102904, d103734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d102904, d103734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d102935 q = 0) : d103760 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d102935, d103760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d102935, d103760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7005 (p : Pattern) (selected : d102937 p = 0) : d103710 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78204 q = 0) : d79072 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78204, d79072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3966 q selected
    | true =>
      simp only [d78204, d79072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78205 q = 0) : d79073 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78205, d79073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78205, d79073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d102907 q = 0) : d103698 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d102907, d103698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d102907, d103698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d102908 q = 0) : d103699 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d102908, d103699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d102908, d103699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d102909 q = 0) : d103700 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d102909, d103700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d102909, d103700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d102937 q = 0) : d103710 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d102937, d103710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d102937, d103710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7006 (p : Pattern) (selected : d102940 p = 0) : d103763 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d102914 q = 0) : d103739 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d102914, d103739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6999 q selected
    | true =>
      simp only [d102914, d103739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d102915 q = 0) : d103740 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d102915, d103740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102915, d103740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d102916 q = 0) : d103741 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d102916, d103741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d102916, d103741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d102917 q = 0) : d103742 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d102917, d103742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d102917, d103742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d102918 q = 0) : d103743 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d102918, d103743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d102918, d103743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d102940 q = 0) : d103763 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d102940, d103763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d102940, d103763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7007 (p : Pattern) (selected : d102946 p = 0) : d103769 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d102892 q = 0) : d103722 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d102892, d103722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6995 q selected
    | true =>
      simp only [d102892, d103722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d102893 q = 0) : d103723 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d102893, d103723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102893, d103723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d102894 q = 0) : d103724 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d102894, d103724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d102894, d103724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d102895 q = 0) : d103725 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102895, d103725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102895, d103725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d102899 q = 0) : d103729 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d102899, d103729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6996 q selected
    | true =>
      simp only [d102899, d103729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d102900 q = 0) : d103730 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d102900, d103730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102900, d103730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d102901 q = 0) : d103731 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d102901, d103731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d102901, d103731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d102906 q = 0) : d103736 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d102906, d103736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6997 q selected
    | true =>
      simp only [d102906, d103736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6991 q selected
  have h9 (q : Pattern) (selected : d102911 q = 0) : d103702 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d102911, d103702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6998 q selected
    | true =>
      simp only [d102911, d103702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d102912 q = 0) : d103737 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d102912, d103737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d102912, d103737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d102920 q = 0) : d103745 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d102920, d103745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7000 q selected
    | true =>
      simp only [d102920, d103745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d102921 q = 0) : d103746 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d102921, d103746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d102921, d103746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d102922 q = 0) : d103747 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d102922, d103747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d102922, d103747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d102923 q = 0) : d103748 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102923, d103748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d102923, d103748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d102924 q = 0) : d103749 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d102924, d103749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d102924, d103749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d102927 q = 0) : d103752 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d102927, d103752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7002 q selected
    | true =>
      simp only [d102927, d103752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d102928 q = 0) : d103753 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d102928, d103753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102928, d103753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d102929 q = 0) : d103754 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d102929, d103754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d102929, d103754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d102930 q = 0) : d103755 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102930, d103755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102930, d103755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d102932 q = 0) : d103757 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d102932, d103757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7003 q selected
    | true =>
      simp only [d102932, d103757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d102933 q = 0) : d103758 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d102933, d103758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102933, d103758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d102934 q = 0) : d103759 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d102934, d103759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d102934, d103759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d102936 q = 0) : d103761 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d102936, d103761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7004 q selected
    | true =>
      simp only [d102936, d103761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6993 q selected
  have h24 (q : Pattern) (selected : d102938 q = 0) : d103711 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d102938, d103711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7005 q selected
    | true =>
      simp only [d102938, d103711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d102939 q = 0) : d103762 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d102939, d103762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d102939, d103762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d102941 q = 0) : d103764 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d102941, d103764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7006 q selected
    | true =>
      simp only [d102941, d103764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d102942 q = 0) : d103765 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d102942, d103765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d102942, d103765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d102943 q = 0) : d103766 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d102943, d103766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d102943, d103766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d102944 q = 0) : d103767 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102944, d103767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d102944, d103767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d102945 q = 0) : d103768 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d102945, d103768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d102945, d103768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d102946 q = 0) : d103769 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d102946, d103769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d102946, d103769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro7008 (p : Pattern) (selected : d102948 p = 0) : d103771 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d102872 q = 0) : d103702 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d102872, d103702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6991 q selected
    | true =>
      simp only [d102872, d103702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d102873 q = 0) : d103703 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d102873, d103703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102873, d103703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d102874 q = 0) : d103704 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d102874, d103704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d102874, d103704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d102875 q = 0) : d103705 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102875, d103705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102875, d103705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d102876 q = 0) : d103706 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d102876, d103706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102876, d103706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d102948 q = 0) : d103771 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d102948, d103771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d102948, d103771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7009 (p : Pattern) (selected : d102955 p = 0) : d103778 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d102936 q = 0) : d103761 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d102936, d103761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7004 q selected
    | true =>
      simp only [d102936, d103761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6993 q selected
  have h2 (q : Pattern) (selected : d102938 q = 0) : d103711 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d102938, d103711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7005 q selected
    | true =>
      simp only [d102938, d103711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d102939 q = 0) : d103762 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d102939, d103762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d102939, d103762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d102941 q = 0) : d103764 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d102941, d103764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7006 q selected
    | true =>
      simp only [d102941, d103764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d102942 q = 0) : d103765 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d102942, d103765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d102942, d103765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d102943 q = 0) : d103766 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d102943, d103766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d102943, d103766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d102953 q = 0) : d103776 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102953, d103776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102953, d103776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d102954 q = 0) : d103777 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d102954, d103777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102954, d103777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d102955 q = 0) : d103778 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d102955, d103778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102955, d103778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7010 (p : Pattern) (selected : d102964 p = 0) : d103787 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78256 q = 0) : d79164 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78256, d79164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3977 q selected
    | true =>
      simp only [d78256, d79164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78257 q = 0) : d79165 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78257, d79165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78257, d79165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d78277 q = 0) : d79177 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78277, d79177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3983 q selected
    | true =>
      simp only [d78277, d79177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d78278 q = 0) : d79178 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78278, d79178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78278, d79178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d102961 q = 0) : d103784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d102961, d103784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d102961, d103784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d102962 q = 0) : d103785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d102962, d103785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d102962, d103785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d102963 q = 0) : d103786 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d102963, d103786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d102963, d103786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d102964 q = 0) : d103787 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d102964, d103787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d102964, d103787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7011 (p : Pattern) (selected : d102968 p = 0) : d103791 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78277 q = 0) : d79177 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78277, d79177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3983 q selected
    | true =>
      simp only [d78277, d79177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78278 q = 0) : d79178 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78278, d79178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78278, d79178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d102965 q = 0) : d103788 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d102965, d103788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d102965, d103788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d102966 q = 0) : d103789 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d102966, d103789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d102966, d103789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d102967 q = 0) : d103790 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d102967, d103790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d102967, d103790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d102968 q = 0) : d103791 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d102968, d103791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d102968, d103791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7012 (p : Pattern) (selected : d102973 p = 0) : d103791 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78269 q = 0) : d79177 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78269, d79177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3981 q selected
    | true =>
      simp only [d78269, d79177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78270 q = 0) : d79178 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78270, d79178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78270, d79178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d102970 q = 0) : d103788 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d102970, d103788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d102970, d103788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d102971 q = 0) : d103789 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d102971, d103789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d102971, d103789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d102972 q = 0) : d103790 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d102972, d103790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d102972, d103790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d102973 q = 0) : d103791 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d102973, d103791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d102973, d103791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7013 (p : Pattern) (selected : d102976 p = 0) : d103795 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d5502 q = 0) : d74228 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5502, d74228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3363 q selected
    | true =>
      simp only [d5502, d74228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3364 q selected
  have h2 (q : Pattern) (selected : d5503 q = 0) : d74229 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5503, d74229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5503, d74229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d5504 q = 0) : d74230 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5504, d74230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5504, d74230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d5505 q = 0) : d74231 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5505, d74231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d5505, d74231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d102976 q = 0) : d103795 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d102976, d103795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d102976, d103795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro7014 (p : Pattern) (selected : d102982 p = 0) : d103801 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d102977 q = 0) : d103796 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d102977, d103796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7013 q selected
    | true =>
      simp only [d102977, d103796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d102978 q = 0) : d103797 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d102978, d103797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102978, d103797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d102979 q = 0) : d103798 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d102979, d103798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d102979, d103798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d102980 q = 0) : d103799 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d102980, d103799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d102980, d103799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d102981 q = 0) : d103800 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d102981, d103800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d102981, d103800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d102982 q = 0) : d103801 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d102982, d103801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d102982, d103801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7015 (p : Pattern) (selected : d102988 p = 0) : d103807 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d102969 q = 0) : d103792 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d102969, d103792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7010 q selected
    | true =>
      simp only [d102969, d103792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7011 q selected
  have h2 (q : Pattern) (selected : d102974 q = 0) : d103793 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d102974, d103793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7012 q selected
    | true =>
      simp only [d102974, d103793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d102975 q = 0) : d103794 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d102975, d103794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d102975, d103794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d102983 q = 0) : d103802 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d102983, d103802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7014 q selected
    | true =>
      simp only [d102983, d103802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d102984 q = 0) : d103803 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d102984, d103803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d102984, d103803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d102985 q = 0) : d103804 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d102985, d103804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d102985, d103804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d102986 q = 0) : d103805 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102986, d103805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102986, d103805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d102987 q = 0) : d103806 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d102987, d103806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102987, d103806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d102988 q = 0) : d103807 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d102988, d103807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102988, d103807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7016 (p : Pattern) (selected : d102994 p = 0) : d103813 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d102878 q = 0) : d103708 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d102878, d103708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102878, d103708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6992 q selected
  have h2 (q : Pattern) (selected : d102879 q = 0) : d103709 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d102879, d103709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d102879, d103709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d102887 q = 0) : d103717 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d102887, d103717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6992 q selected
    | true =>
      simp only [d102887, d103717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6994 q selected
  have h4 (q : Pattern) (selected : d102888 q = 0) : d103718 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d102888, d103718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d102888, d103718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d102889 q = 0) : d103719 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d102889, d103719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d102889, d103719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d102947 q = 0) : d103770 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d102947, d103770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7001 q selected
    | true =>
      simp only [d102947, d103770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7007 q selected
  have h7 (q : Pattern) (selected : d102949 q = 0) : d103772 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d102949, d103772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7008 q selected
    | true =>
      simp only [d102949, d103772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d102950 q = 0) : d103773 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d102950, d103773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d102950, d103773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d102951 q = 0) : d103774 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d102951, d103774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d102951, d103774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d102952 q = 0) : d103775 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d102952, d103775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d102952, d103775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d102956 q = 0) : d103779 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d102956, d103779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102956, d103779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7009 q selected
  have h12 (q : Pattern) (selected : d102957 q = 0) : d103780 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d102957, d103780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d102957, d103780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d102958 q = 0) : d103781 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d102958, d103781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d102958, d103781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d102959 q = 0) : d103782 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d102959, d103782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d102959, d103782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d102960 q = 0) : d103783 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d102960, d103783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d102960, d103783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d102989 q = 0) : d103808 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d102989, d103808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102989, d103808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7015 q selected
  have h17 (q : Pattern) (selected : d102990 q = 0) : d103809 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d102990, d103809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d102990, d103809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d102991 q = 0) : d103810 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d102991, d103810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d102991, d103810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d102992 q = 0) : d103811 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d102992, d103811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d102992, d103811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d102993 q = 0) : d103812 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d102993, d103812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d102993, d103812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d102994 q = 0) : d103813 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d102994, d103813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d102994, d103813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro7017 (p : Pattern) (selected : d103000 p = 0) : d103819 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d102995 q = 0) : d103814 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d102995, d103814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102995, d103814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7016 q selected
  have h2 (q : Pattern) (selected : d102996 q = 0) : d103815 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d102996, d103815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102996, d103815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d102997 q = 0) : d103816 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d102997, d103816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102997, d103816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d102998 q = 0) : d103817 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d102998, d103817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102998, d103817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d102999 q = 0) : d103818 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d102999, d103818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102999, d103818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103000 q = 0) : d103819 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d103000, d103819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103000, d103819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7018 (p : Pattern) (selected : d103006 p = 0) : d103825 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78303 q = 0) : d79204 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78303, d79204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3988 q selected
    | true =>
      simp only [d78303, d79204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78304 q = 0) : d79205 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78304, d79205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78304, d79205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103003 q = 0) : d103822 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103003, d103822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103003, d103822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103004 q = 0) : d103823 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103004, d103823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103004, d103823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103005 q = 0) : d103824 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103005, d103824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103005, d103824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103006 q = 0) : d103825 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103006, d103825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103006, d103825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7019 (p : Pattern) (selected : d103012 p = 0) : d103831 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103007 q = 0) : d103826 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103007, d103826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7018 q selected
    | true =>
      simp only [d103007, d103826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d103008 q = 0) : d103827 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103008, d103827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103008, d103827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103009 q = 0) : d103828 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103009, d103828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103009, d103828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103010 q = 0) : d103829 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103010, d103829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103010, d103829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d103011 q = 0) : d103830 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103011, d103830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103011, d103830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103012 q = 0) : d103831 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d103012, d103831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103012, d103831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7020 (p : Pattern) (selected : d103015 p = 0) : d103834 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78303 q = 0) : d79204 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78303, d79204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3988 q selected
    | true =>
      simp only [d78303, d79204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78304 q = 0) : d79205 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78304, d79205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78304, d79205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103003 q = 0) : d103822 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103003, d103822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103003, d103822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103004 q = 0) : d103823 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103004, d103823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103004, d103823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103005 q = 0) : d103824 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103005, d103824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103005, d103824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103015 q = 0) : d103834 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103015, d103834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103015, d103834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7021 (p : Pattern) (selected : d103021 p = 0) : d103840 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103007 q = 0) : d103826 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103007, d103826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7018 q selected
    | true =>
      simp only [d103007, d103826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d103008 q = 0) : d103827 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103008, d103827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103008, d103827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103009 q = 0) : d103828 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103009, d103828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103009, d103828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103010 q = 0) : d103829 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103010, d103829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103010, d103829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d103011 q = 0) : d103830 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103011, d103830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103011, d103830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103016 q = 0) : d103835 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103016, d103835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7020 q selected
    | true =>
      simp only [d103016, d103835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d103017 q = 0) : d103836 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103017, d103836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103017, d103836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d103018 q = 0) : d103837 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103018, d103837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d103018, d103837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d103019 q = 0) : d103838 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103019, d103838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103019, d103838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d103020 q = 0) : d103839 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103020, d103839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103020, d103839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d103021 q = 0) : d103840 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d103021, d103840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103021, d103840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7022 (p : Pattern) (selected : d103026 p = 0) : d103845 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78303 q = 0) : d79204 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78303, d79204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3988 q selected
    | true =>
      simp only [d78303, d79204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78304 q = 0) : d79205 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78304, d79205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78304, d79205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103003 q = 0) : d103822 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103003, d103822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103003, d103822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103004 q = 0) : d103823 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103004, d103823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103004, d103823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103025 q = 0) : d103844 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103025, d103844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103025, d103844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103026 q = 0) : d103845 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103026, d103845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103026, d103845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7023 (p : Pattern) (selected : d103033 p = 0) : d103852 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78303 q = 0) : d79204 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78303, d79204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3988 q selected
    | true =>
      simp only [d78303, d79204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78304 q = 0) : d79205 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78304, d79205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78304, d79205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103003 q = 0) : d103822 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103003, d103822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103003, d103822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103031 q = 0) : d103850 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103031, d103850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103031, d103850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d103032 q = 0) : d103851 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103032, d103851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103032, d103851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103033 q = 0) : d103852 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103033, d103852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103033, d103852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7024 (p : Pattern) (selected : d103040 p = 0) : d103859 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78339 q = 0) : d79240 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78339, d79240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3995 q selected
    | true =>
      simp only [d78339, d79240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78340 q = 0) : d79241 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78340, d79241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78340, d79241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d78303 q = 0) : d79204 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78303, d79204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3988 q selected
    | true =>
      simp only [d78303, d79204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d78304 q = 0) : d79205 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78304, d79205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78304, d79205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d103037 q = 0) : d103856 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103037, d103856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103037, d103856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103038 q = 0) : d103857 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103038, d103857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103038, d103857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d103039 q = 0) : d103858 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103039, d103858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d103039, d103858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d103040 q = 0) : d103859 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103040, d103859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103040, d103859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7025 (p : Pattern) (selected : d103045 p = 0) : d103825 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78352 q = 0) : d79204 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78352, d79204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3999 q selected
    | true =>
      simp only [d78352, d79204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78353 q = 0) : d79205 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78353, d79205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78353, d79205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103042 q = 0) : d103822 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103042, d103822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103042, d103822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103043 q = 0) : d103823 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103043, d103823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103043, d103823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103044 q = 0) : d103824 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103044, d103824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103044, d103824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103045 q = 0) : d103825 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103045, d103825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103045, d103825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7026 (p : Pattern) (selected : d103048 p = 0) : d103862 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d5547 q = 0) : d74273 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5547, d74273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3371 q selected
    | true =>
      simp only [d5547, d74273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3372 q selected
  have h2 (q : Pattern) (selected : d5548 q = 0) : d74274 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5548, d74274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5548, d74274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d5549 q = 0) : d74275 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5549, d74275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5549, d74275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d5550 q = 0) : d74276 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5550, d74276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d5550, d74276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103048 q = 0) : d103862 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d103048, d103862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103048, d103862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro7027 (p : Pattern) (selected : d103054 p = 0) : d103868 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103049 q = 0) : d103863 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d103049, d103863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7026 q selected
    | true =>
      simp only [d103049, d103863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d103050 q = 0) : d103864 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d103050, d103864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103050, d103864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103051 q = 0) : d103865 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103051, d103865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103051, d103865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103052 q = 0) : d103866 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103052, d103866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103052, d103866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103053 q = 0) : d103867 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103053, d103867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103053, d103867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103054 q = 0) : d103868 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103054, d103868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103054, d103868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7028 (p : Pattern) (selected : d103060 p = 0) : d103874 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103027 q = 0) : d103846 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103027, d103846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7022 q selected
    | true =>
      simp only [d103027, d103846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d103028 q = 0) : d103847 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103028, d103847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103028, d103847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103029 q = 0) : d103848 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103029, d103848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103029, d103848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103030 q = 0) : d103849 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103030, d103849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103030, d103849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d103034 q = 0) : d103853 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103034, d103853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7023 q selected
    | true =>
      simp only [d103034, d103853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103035 q = 0) : d103854 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103035, d103854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103035, d103854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d103036 q = 0) : d103855 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103036, d103855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d103036, d103855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d103041 q = 0) : d103860 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103041, d103860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7024 q selected
    | true =>
      simp only [d103041, d103860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7018 q selected
  have h9 (q : Pattern) (selected : d103046 q = 0) : d103826 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103046, d103826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7025 q selected
    | true =>
      simp only [d103046, d103826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d103047 q = 0) : d103861 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103047, d103861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d103047, d103861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d103055 q = 0) : d103869 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103055, d103869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7027 q selected
    | true =>
      simp only [d103055, d103869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d103056 q = 0) : d103870 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103056, d103870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d103056, d103870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d103057 q = 0) : d103871 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103057, d103871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d103057, d103871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d103058 q = 0) : d103872 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103058, d103872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d103058, d103872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d103059 q = 0) : d103873 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103059, d103873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103059, d103873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d103060 q = 0) : d103874 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d103060, d103874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103060, d103874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro7029 (p : Pattern) (selected : d103061 p = 0) : d103875 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78303 q = 0) : d79204 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78303, d79204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3988 q selected
    | true =>
      simp only [d78303, d79204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78304 q = 0) : d79205 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78304, d79205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78304, d79205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103003 q = 0) : d103822 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103003, d103822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103003, d103822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103004 q = 0) : d103823 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103004, d103823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103004, d103823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103025 q = 0) : d103844 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103025, d103844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103025, d103844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103061 q = 0) : d103875 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103061, d103875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103061, d103875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7030 (p : Pattern) (selected : d103066 p = 0) : d103880 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78303 q = 0) : d79204 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78303, d79204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3988 q selected
    | true =>
      simp only [d78303, d79204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78304 q = 0) : d79205 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78304, d79205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78304, d79205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103003 q = 0) : d103822 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103003, d103822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103003, d103822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103031 q = 0) : d103850 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103031, d103850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103031, d103850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d103032 q = 0) : d103851 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103032, d103851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103032, d103851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103066 q = 0) : d103880 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103066, d103880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103066, d103880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7031 (p : Pattern) (selected : d103070 p = 0) : d103884 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78339 q = 0) : d79240 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78339, d79240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3995 q selected
    | true =>
      simp only [d78339, d79240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78340 q = 0) : d79241 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78340, d79241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78340, d79241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d78303 q = 0) : d79204 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78303, d79204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3988 q selected
    | true =>
      simp only [d78303, d79204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d78304 q = 0) : d79205 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78304, d79205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78304, d79205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d103037 q = 0) : d103856 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103037, d103856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103037, d103856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103038 q = 0) : d103857 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103038, d103857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103038, d103857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d103039 q = 0) : d103858 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103039, d103858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d103039, d103858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d103070 q = 0) : d103884 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103070, d103884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d103070, d103884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7032 (p : Pattern) (selected : d103072 p = 0) : d103834 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78352 q = 0) : d79204 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78352, d79204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3999 q selected
    | true =>
      simp only [d78352, d79204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78353 q = 0) : d79205 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78353, d79205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78353, d79205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103042 q = 0) : d103822 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103042, d103822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103042, d103822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103043 q = 0) : d103823 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103043, d103823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103043, d103823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103044 q = 0) : d103824 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103044, d103824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103044, d103824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103072 q = 0) : d103834 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103072, d103834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103072, d103834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7033 (p : Pattern) (selected : d103075 p = 0) : d103887 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103049 q = 0) : d103863 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d103049, d103863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7026 q selected
    | true =>
      simp only [d103049, d103863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d103050 q = 0) : d103864 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d103050, d103864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103050, d103864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103051 q = 0) : d103865 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103051, d103865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103051, d103865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103052 q = 0) : d103866 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103052, d103866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103052, d103866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103053 q = 0) : d103867 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103053, d103867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103053, d103867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103075 q = 0) : d103887 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103075, d103887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103075, d103887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7034 (p : Pattern) (selected : d103081 p = 0) : d103893 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103027 q = 0) : d103846 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103027, d103846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7022 q selected
    | true =>
      simp only [d103027, d103846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d103028 q = 0) : d103847 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103028, d103847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103028, d103847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103029 q = 0) : d103848 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103029, d103848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103029, d103848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103030 q = 0) : d103849 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103030, d103849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103030, d103849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d103034 q = 0) : d103853 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103034, d103853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7023 q selected
    | true =>
      simp only [d103034, d103853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103035 q = 0) : d103854 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103035, d103854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103035, d103854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d103036 q = 0) : d103855 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103036, d103855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d103036, d103855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d103041 q = 0) : d103860 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103041, d103860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7024 q selected
    | true =>
      simp only [d103041, d103860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7018 q selected
  have h9 (q : Pattern) (selected : d103046 q = 0) : d103826 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103046, d103826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7025 q selected
    | true =>
      simp only [d103046, d103826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d103047 q = 0) : d103861 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103047, d103861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d103047, d103861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d103055 q = 0) : d103869 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103055, d103869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7027 q selected
    | true =>
      simp only [d103055, d103869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d103056 q = 0) : d103870 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103056, d103870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d103056, d103870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d103057 q = 0) : d103871 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103057, d103871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d103057, d103871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d103058 q = 0) : d103872 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103058, d103872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d103058, d103872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d103059 q = 0) : d103873 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103059, d103873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103059, d103873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d103062 q = 0) : d103876 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103062, d103876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7029 q selected
    | true =>
      simp only [d103062, d103876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d103063 q = 0) : d103877 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103063, d103877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103063, d103877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d103064 q = 0) : d103878 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103064, d103878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d103064, d103878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d103065 q = 0) : d103879 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103065, d103879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103065, d103879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d103067 q = 0) : d103881 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103067, d103881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7030 q selected
    | true =>
      simp only [d103067, d103881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d103068 q = 0) : d103882 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103068, d103882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103068, d103882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d103069 q = 0) : d103883 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103069, d103883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d103069, d103883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d103071 q = 0) : d103885 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103071, d103885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7031 q selected
    | true =>
      simp only [d103071, d103885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7020 q selected
  have h24 (q : Pattern) (selected : d103073 q = 0) : d103835 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103073, d103835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7032 q selected
    | true =>
      simp only [d103073, d103835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d103074 q = 0) : d103886 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103074, d103886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d103074, d103886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d103076 q = 0) : d103888 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103076, d103888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7033 q selected
    | true =>
      simp only [d103076, d103888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d103077 q = 0) : d103889 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103077, d103889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d103077, d103889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d103078 q = 0) : d103890 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103078, d103890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d103078, d103890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d103079 q = 0) : d103891 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103079, d103891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d103079, d103891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d103080 q = 0) : d103892 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103080, d103892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d103080, d103892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d103081 q = 0) : d103893 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d103081, d103893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d103081, d103893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro7035 (p : Pattern) (selected : d103083 p = 0) : d103895 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103007 q = 0) : d103826 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103007, d103826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7018 q selected
    | true =>
      simp only [d103007, d103826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d103008 q = 0) : d103827 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103008, d103827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103008, d103827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103009 q = 0) : d103828 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103009, d103828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103009, d103828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103010 q = 0) : d103829 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103010, d103829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103010, d103829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d103011 q = 0) : d103830 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103011, d103830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103011, d103830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103083 q = 0) : d103895 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d103083, d103895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103083, d103895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7036 (p : Pattern) (selected : d103090 p = 0) : d103902 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103071 q = 0) : d103885 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103071, d103885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7031 q selected
    | true =>
      simp only [d103071, d103885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7020 q selected
  have h2 (q : Pattern) (selected : d103073 q = 0) : d103835 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103073, d103835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7032 q selected
    | true =>
      simp only [d103073, d103835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d103074 q = 0) : d103886 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103074, d103886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103074, d103886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d103076 q = 0) : d103888 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103076, d103888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7033 q selected
    | true =>
      simp only [d103076, d103888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103077 q = 0) : d103889 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103077, d103889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103077, d103889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103078 q = 0) : d103890 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103078, d103890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103078, d103890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d103088 q = 0) : d103900 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103088, d103900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103088, d103900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d103089 q = 0) : d103901 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103089, d103901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103089, d103901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d103090 q = 0) : d103902 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d103090, d103902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103090, d103902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7037 (p : Pattern) (selected : d103099 p = 0) : d103911 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78404 q = 0) : d79296 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78404, d79296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4010 q selected
    | true =>
      simp only [d78404, d79296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78405 q = 0) : d79297 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78405, d79297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78405, d79297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d78425 q = 0) : d79309 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78425, d79309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4016 q selected
    | true =>
      simp only [d78425, d79309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d78426 q = 0) : d79310 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78426, d79310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78426, d79310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d103096 q = 0) : d103908 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103096, d103908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103096, d103908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103097 q = 0) : d103909 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103097, d103909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103097, d103909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d103098 q = 0) : d103910 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103098, d103910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d103098, d103910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d103099 q = 0) : d103911 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103099, d103911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d103099, d103911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7038 (p : Pattern) (selected : d103103 p = 0) : d103915 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78425 q = 0) : d79309 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78425, d79309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4016 q selected
    | true =>
      simp only [d78425, d79309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78426 q = 0) : d79310 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78426, d79310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78426, d79310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103100 q = 0) : d103912 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103100, d103912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103100, d103912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103101 q = 0) : d103913 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103101, d103913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103101, d103913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103102 q = 0) : d103914 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103102, d103914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103102, d103914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103103 q = 0) : d103915 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103103, d103915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103103, d103915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7039 (p : Pattern) (selected : d103108 p = 0) : d103915 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78417 q = 0) : d79309 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78417, d79309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4014 q selected
    | true =>
      simp only [d78417, d79309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78418 q = 0) : d79310 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78418, d79310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78418, d79310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103105 q = 0) : d103912 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103105, d103912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103105, d103912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103106 q = 0) : d103913 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103106, d103913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103106, d103913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103107 q = 0) : d103914 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103107, d103914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103107, d103914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103108 q = 0) : d103915 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103108, d103915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103108, d103915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7040 (p : Pattern) (selected : d103111 p = 0) : d103919 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d5591 q = 0) : d74317 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5591, d74317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3379 q selected
    | true =>
      simp only [d5591, d74317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3380 q selected
  have h2 (q : Pattern) (selected : d5592 q = 0) : d74318 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5592, d74318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5592, d74318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d5593 q = 0) : d74319 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5593, d74319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5593, d74319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d5594 q = 0) : d74320 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5594, d74320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d5594, d74320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103111 q = 0) : d103919 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d103111, d103919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103111, d103919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro7041 (p : Pattern) (selected : d103117 p = 0) : d103925 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103112 q = 0) : d103920 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d103112, d103920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7040 q selected
    | true =>
      simp only [d103112, d103920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d103113 q = 0) : d103921 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d103113, d103921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103113, d103921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103114 q = 0) : d103922 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103114, d103922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103114, d103922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103115 q = 0) : d103923 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103115, d103923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103115, d103923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103116 q = 0) : d103924 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103116, d103924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103116, d103924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103117 q = 0) : d103925 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103117, d103925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103117, d103925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7042 (p : Pattern) (selected : d103123 p = 0) : d103931 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103104 q = 0) : d103916 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103104, d103916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7037 q selected
    | true =>
      simp only [d103104, d103916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7038 q selected
  have h2 (q : Pattern) (selected : d103109 q = 0) : d103917 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103109, d103917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7039 q selected
    | true =>
      simp only [d103109, d103917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d103110 q = 0) : d103918 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103110, d103918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103110, d103918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d103118 q = 0) : d103926 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103118, d103926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7041 q selected
    | true =>
      simp only [d103118, d103926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103119 q = 0) : d103927 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103119, d103927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103119, d103927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103120 q = 0) : d103928 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103120, d103928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103120, d103928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d103121 q = 0) : d103929 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103121, d103929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103121, d103929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d103122 q = 0) : d103930 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103122, d103930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103122, d103930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d103123 q = 0) : d103931 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d103123, d103931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103123, d103931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7043 (p : Pattern) (selected : d103129 p = 0) : d103937 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103013 q = 0) : d103832 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d103013, d103832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103013, d103832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7019 q selected
  have h2 (q : Pattern) (selected : d103014 q = 0) : d103833 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d103014, d103833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103014, d103833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d103022 q = 0) : d103841 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d103022, d103841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7019 q selected
    | true =>
      simp only [d103022, d103841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7021 q selected
  have h4 (q : Pattern) (selected : d103023 q = 0) : d103842 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d103023, d103842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103023, d103842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103024 q = 0) : d103843 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d103024, d103843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103024, d103843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103082 q = 0) : d103894 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d103082, d103894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7028 q selected
    | true =>
      simp only [d103082, d103894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7034 q selected
  have h7 (q : Pattern) (selected : d103084 q = 0) : d103896 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d103084, d103896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7035 q selected
    | true =>
      simp only [d103084, d103896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d103085 q = 0) : d103897 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d103085, d103897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d103085, d103897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d103086 q = 0) : d103898 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d103086, d103898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d103086, d103898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d103087 q = 0) : d103899 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d103087, d103899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103087, d103899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d103091 q = 0) : d103903 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d103091, d103903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103091, d103903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7036 q selected
  have h12 (q : Pattern) (selected : d103092 q = 0) : d103904 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d103092, d103904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d103092, d103904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d103093 q = 0) : d103905 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d103093, d103905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d103093, d103905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d103094 q = 0) : d103906 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d103094, d103906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d103094, d103906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d103095 q = 0) : d103907 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d103095, d103907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d103095, d103907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d103124 q = 0) : d103932 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d103124, d103932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103124, d103932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7042 q selected
  have h17 (q : Pattern) (selected : d103125 q = 0) : d103933 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d103125, d103933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d103125, d103933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d103126 q = 0) : d103934 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d103126, d103934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d103126, d103934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d103127 q = 0) : d103935 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d103127, d103935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d103127, d103935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d103128 q = 0) : d103936 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d103128, d103936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d103128, d103936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d103129 q = 0) : d103937 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d103129, d103937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d103129, d103937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro7044 (p : Pattern) (selected : d103135 p = 0) : d103943 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103130 q = 0) : d103938 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d103130, d103938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103130, d103938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7043 q selected
  have h2 (q : Pattern) (selected : d103131 q = 0) : d103939 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d103131, d103939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103131, d103939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103132 q = 0) : d103940 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d103132, d103940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103132, d103940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d103133 q = 0) : d103941 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d103133, d103941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103133, d103941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d103134 q = 0) : d103942 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d103134, d103942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103134, d103942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103135 q = 0) : d103943 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d103135, d103943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103135, d103943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7045 (p : Pattern) (selected : d103142 p = 0) : d103950 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78452 q = 0) : d79337 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78452, d79337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4021 q selected
    | true =>
      simp only [d78452, d79337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78453 q = 0) : d79338 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78453, d79338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78453, d79338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103139 q = 0) : d103947 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103139, d103947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103139, d103947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103140 q = 0) : d103948 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103140, d103948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103140, d103948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103141 q = 0) : d103949 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103141, d103949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103141, d103949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103142 q = 0) : d103950 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103142, d103950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103142, d103950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7046 (p : Pattern) (selected : d103148 p = 0) : d103956 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103143 q = 0) : d103951 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103143, d103951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7045 q selected
    | true =>
      simp only [d103143, d103951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d103144 q = 0) : d103952 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103144, d103952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103144, d103952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103145 q = 0) : d103953 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103145, d103953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103145, d103953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103146 q = 0) : d103954 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103146, d103954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103146, d103954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d103147 q = 0) : d103955 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103147, d103955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103147, d103955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103148 q = 0) : d103956 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d103148, d103956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103148, d103956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7047 (p : Pattern) (selected : d103151 p = 0) : d103959 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78452 q = 0) : d79337 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78452, d79337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4021 q selected
    | true =>
      simp only [d78452, d79337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78453 q = 0) : d79338 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78453, d79338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78453, d79338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103139 q = 0) : d103947 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103139, d103947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103139, d103947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103140 q = 0) : d103948 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103140, d103948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103140, d103948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103141 q = 0) : d103949 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103141, d103949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103141, d103949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103151 q = 0) : d103959 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103151, d103959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103151, d103959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7048 (p : Pattern) (selected : d103157 p = 0) : d103965 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103143 q = 0) : d103951 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103143, d103951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7045 q selected
    | true =>
      simp only [d103143, d103951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d103144 q = 0) : d103952 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103144, d103952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103144, d103952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103145 q = 0) : d103953 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103145, d103953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103145, d103953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103146 q = 0) : d103954 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103146, d103954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103146, d103954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d103147 q = 0) : d103955 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103147, d103955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103147, d103955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103152 q = 0) : d103960 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103152, d103960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7047 q selected
    | true =>
      simp only [d103152, d103960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d103153 q = 0) : d103961 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103153, d103961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103153, d103961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d103154 q = 0) : d103962 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103154, d103962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d103154, d103962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d103155 q = 0) : d103963 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103155, d103963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103155, d103963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d103156 q = 0) : d103964 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103156, d103964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103156, d103964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d103157 q = 0) : d103965 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d103157, d103965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103157, d103965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7049 (p : Pattern) (selected : d103162 p = 0) : d103970 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78452 q = 0) : d79337 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78452, d79337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4021 q selected
    | true =>
      simp only [d78452, d79337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78453 q = 0) : d79338 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78453, d79338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78453, d79338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103139 q = 0) : d103947 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103139, d103947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103139, d103947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103140 q = 0) : d103948 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103140, d103948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103140, d103948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103161 q = 0) : d103969 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103161, d103969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103161, d103969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103162 q = 0) : d103970 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103162, d103970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103162, d103970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7050 (p : Pattern) (selected : d103169 p = 0) : d103977 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78452 q = 0) : d79337 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78452, d79337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4021 q selected
    | true =>
      simp only [d78452, d79337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78453 q = 0) : d79338 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78453, d79338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78453, d79338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103139 q = 0) : d103947 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103139, d103947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103139, d103947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103167 q = 0) : d103975 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103167, d103975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103167, d103975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d103168 q = 0) : d103976 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103168, d103976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103168, d103976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103169 q = 0) : d103977 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103169, d103977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103169, d103977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7051 (p : Pattern) (selected : d103176 p = 0) : d103984 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78488 q = 0) : d79373 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78488, d79373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4028 q selected
    | true =>
      simp only [d78488, d79373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78489 q = 0) : d79374 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78489, d79374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78489, d79374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d78452 q = 0) : d79337 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78452, d79337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4021 q selected
    | true =>
      simp only [d78452, d79337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d78453 q = 0) : d79338 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78453, d79338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78453, d79338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d103173 q = 0) : d103981 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103173, d103981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103173, d103981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103174 q = 0) : d103982 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103174, d103982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103174, d103982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d103175 q = 0) : d103983 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103175, d103983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d103175, d103983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d103176 q = 0) : d103984 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103176, d103984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103176, d103984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7052 (p : Pattern) (selected : d103181 p = 0) : d103950 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78501 q = 0) : d79337 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78501, d79337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4032 q selected
    | true =>
      simp only [d78501, d79337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78502 q = 0) : d79338 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78502, d79338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78502, d79338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103178 q = 0) : d103947 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103178, d103947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103178, d103947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103179 q = 0) : d103948 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103179, d103948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103179, d103948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103180 q = 0) : d103949 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103180, d103949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103180, d103949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103181 q = 0) : d103950 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103181, d103950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103181, d103950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7053 (p : Pattern) (selected : d103184 p = 0) : d103987 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d5637 q = 0) : d74363 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5637, d74363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3387 q selected
    | true =>
      simp only [d5637, d74363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3388 q selected
  have h2 (q : Pattern) (selected : d5638 q = 0) : d74364 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5638, d74364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5638, d74364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d5639 q = 0) : d74365 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5639, d74365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5639, d74365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d5640 q = 0) : d74366 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5640, d74366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d5640, d74366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103184 q = 0) : d103987 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d103184, d103987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103184, d103987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro7054 (p : Pattern) (selected : d103190 p = 0) : d103993 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103185 q = 0) : d103988 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d103185, d103988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7053 q selected
    | true =>
      simp only [d103185, d103988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d103186 q = 0) : d103989 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d103186, d103989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103186, d103989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103187 q = 0) : d103990 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103187, d103990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103187, d103990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103188 q = 0) : d103991 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103188, d103991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103188, d103991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103189 q = 0) : d103992 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103189, d103992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103189, d103992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103190 q = 0) : d103993 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103190, d103993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103190, d103993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7055 (p : Pattern) (selected : d103196 p = 0) : d103999 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103163 q = 0) : d103971 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103163, d103971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7049 q selected
    | true =>
      simp only [d103163, d103971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d103164 q = 0) : d103972 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103164, d103972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103164, d103972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103165 q = 0) : d103973 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103165, d103973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103165, d103973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103166 q = 0) : d103974 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103166, d103974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103166, d103974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d103170 q = 0) : d103978 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103170, d103978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7050 q selected
    | true =>
      simp only [d103170, d103978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103171 q = 0) : d103979 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103171, d103979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103171, d103979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d103172 q = 0) : d103980 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103172, d103980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d103172, d103980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d103177 q = 0) : d103985 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103177, d103985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7051 q selected
    | true =>
      simp only [d103177, d103985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7045 q selected
  have h9 (q : Pattern) (selected : d103182 q = 0) : d103951 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103182, d103951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7052 q selected
    | true =>
      simp only [d103182, d103951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d103183 q = 0) : d103986 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103183, d103986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d103183, d103986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d103191 q = 0) : d103994 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103191, d103994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7054 q selected
    | true =>
      simp only [d103191, d103994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d103192 q = 0) : d103995 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103192, d103995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d103192, d103995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d103193 q = 0) : d103996 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103193, d103996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d103193, d103996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d103194 q = 0) : d103997 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103194, d103997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d103194, d103997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d103195 q = 0) : d103998 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103195, d103998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103195, d103998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d103196 q = 0) : d103999 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d103196, d103999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103196, d103999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro7056 (p : Pattern) (selected : d103197 p = 0) : d104000 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78452 q = 0) : d79337 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78452, d79337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4021 q selected
    | true =>
      simp only [d78452, d79337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78453 q = 0) : d79338 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78453, d79338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78453, d79338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103139 q = 0) : d103947 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103139, d103947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103139, d103947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103140 q = 0) : d103948 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103140, d103948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103140, d103948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103161 q = 0) : d103969 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103161, d103969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103161, d103969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103197 q = 0) : d104000 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103197, d104000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103197, d104000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7057 (p : Pattern) (selected : d103202 p = 0) : d104005 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78452 q = 0) : d79337 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78452, d79337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4021 q selected
    | true =>
      simp only [d78452, d79337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78453 q = 0) : d79338 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78453, d79338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78453, d79338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103139 q = 0) : d103947 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103139, d103947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103139, d103947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103167 q = 0) : d103975 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103167, d103975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103167, d103975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d103168 q = 0) : d103976 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103168, d103976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103168, d103976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103202 q = 0) : d104005 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103202, d104005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103202, d104005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7058 (p : Pattern) (selected : d103206 p = 0) : d104009 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78488 q = 0) : d79373 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78488, d79373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4028 q selected
    | true =>
      simp only [d78488, d79373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78489 q = 0) : d79374 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78489, d79374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78489, d79374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d78452 q = 0) : d79337 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78452, d79337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4021 q selected
    | true =>
      simp only [d78452, d79337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d78453 q = 0) : d79338 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78453, d79338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78453, d79338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d103173 q = 0) : d103981 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103173, d103981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103173, d103981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103174 q = 0) : d103982 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103174, d103982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103174, d103982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d103175 q = 0) : d103983 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103175, d103983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d103175, d103983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d103206 q = 0) : d104009 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103206, d104009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d103206, d104009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7059 (p : Pattern) (selected : d103208 p = 0) : d103959 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78501 q = 0) : d79337 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78501, d79337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4032 q selected
    | true =>
      simp only [d78501, d79337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78502 q = 0) : d79338 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78502, d79338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78502, d79338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103178 q = 0) : d103947 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103178, d103947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103178, d103947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103179 q = 0) : d103948 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103179, d103948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103179, d103948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103180 q = 0) : d103949 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103180, d103949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103180, d103949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103208 q = 0) : d103959 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103208, d103959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103208, d103959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7060 (p : Pattern) (selected : d103211 p = 0) : d104012 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103185 q = 0) : d103988 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d103185, d103988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7053 q selected
    | true =>
      simp only [d103185, d103988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d103186 q = 0) : d103989 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d103186, d103989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103186, d103989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103187 q = 0) : d103990 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103187, d103990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103187, d103990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103188 q = 0) : d103991 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103188, d103991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103188, d103991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103189 q = 0) : d103992 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103189, d103992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103189, d103992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103211 q = 0) : d104012 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103211, d104012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103211, d104012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7061 (p : Pattern) (selected : d103217 p = 0) : d104018 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103163 q = 0) : d103971 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103163, d103971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7049 q selected
    | true =>
      simp only [d103163, d103971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d103164 q = 0) : d103972 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103164, d103972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103164, d103972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103165 q = 0) : d103973 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103165, d103973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103165, d103973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103166 q = 0) : d103974 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103166, d103974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103166, d103974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d103170 q = 0) : d103978 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103170, d103978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7050 q selected
    | true =>
      simp only [d103170, d103978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103171 q = 0) : d103979 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103171, d103979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103171, d103979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d103172 q = 0) : d103980 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103172, d103980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d103172, d103980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d103177 q = 0) : d103985 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103177, d103985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7051 q selected
    | true =>
      simp only [d103177, d103985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7045 q selected
  have h9 (q : Pattern) (selected : d103182 q = 0) : d103951 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103182, d103951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7052 q selected
    | true =>
      simp only [d103182, d103951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d103183 q = 0) : d103986 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103183, d103986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d103183, d103986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d103191 q = 0) : d103994 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103191, d103994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7054 q selected
    | true =>
      simp only [d103191, d103994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d103192 q = 0) : d103995 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103192, d103995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d103192, d103995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d103193 q = 0) : d103996 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103193, d103996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d103193, d103996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d103194 q = 0) : d103997 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103194, d103997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d103194, d103997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d103195 q = 0) : d103998 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103195, d103998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103195, d103998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d103198 q = 0) : d104001 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103198, d104001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7056 q selected
    | true =>
      simp only [d103198, d104001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d103199 q = 0) : d104002 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103199, d104002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103199, d104002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d103200 q = 0) : d104003 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103200, d104003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d103200, d104003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d103201 q = 0) : d104004 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103201, d104004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103201, d104004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d103203 q = 0) : d104006 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103203, d104006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7057 q selected
    | true =>
      simp only [d103203, d104006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d103204 q = 0) : d104007 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103204, d104007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103204, d104007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d103205 q = 0) : d104008 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103205, d104008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d103205, d104008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d103207 q = 0) : d104010 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103207, d104010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7058 q selected
    | true =>
      simp only [d103207, d104010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7047 q selected
  have h24 (q : Pattern) (selected : d103209 q = 0) : d103960 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103209, d103960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7059 q selected
    | true =>
      simp only [d103209, d103960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d103210 q = 0) : d104011 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103210, d104011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d103210, d104011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d103212 q = 0) : d104013 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103212, d104013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7060 q selected
    | true =>
      simp only [d103212, d104013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d103213 q = 0) : d104014 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103213, d104014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d103213, d104014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d103214 q = 0) : d104015 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103214, d104015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d103214, d104015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d103215 q = 0) : d104016 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103215, d104016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d103215, d104016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d103216 q = 0) : d104017 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103216, d104017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d103216, d104017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d103217 q = 0) : d104018 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d103217, d104018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d103217, d104018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro7062 (p : Pattern) (selected : d103219 p = 0) : d104020 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103143 q = 0) : d103951 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103143, d103951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7045 q selected
    | true =>
      simp only [d103143, d103951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d103144 q = 0) : d103952 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103144, d103952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103144, d103952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103145 q = 0) : d103953 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103145, d103953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103145, d103953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103146 q = 0) : d103954 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103146, d103954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103146, d103954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d103147 q = 0) : d103955 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103147, d103955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103147, d103955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103219 q = 0) : d104020 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d103219, d104020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103219, d104020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7063 (p : Pattern) (selected : d103226 p = 0) : d104027 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103207 q = 0) : d104010 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103207, d104010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7058 q selected
    | true =>
      simp only [d103207, d104010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7047 q selected
  have h2 (q : Pattern) (selected : d103209 q = 0) : d103960 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103209, d103960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7059 q selected
    | true =>
      simp only [d103209, d103960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d103210 q = 0) : d104011 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103210, d104011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103210, d104011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d103212 q = 0) : d104013 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103212, d104013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7060 q selected
    | true =>
      simp only [d103212, d104013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103213 q = 0) : d104014 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103213, d104014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103213, d104014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103214 q = 0) : d104015 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103214, d104015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103214, d104015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d103224 q = 0) : d104025 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103224, d104025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103224, d104025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d103225 q = 0) : d104026 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103225, d104026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103225, d104026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d103226 q = 0) : d104027 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d103226, d104027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103226, d104027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7064 (p : Pattern) (selected : d103235 p = 0) : d104036 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78553 q = 0) : d79429 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78553, d79429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4043 q selected
    | true =>
      simp only [d78553, d79429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78554 q = 0) : d79430 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78554, d79430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78554, d79430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d78574 q = 0) : d79442 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78574, d79442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4049 q selected
    | true =>
      simp only [d78574, d79442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d78575 q = 0) : d79443 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78575, d79443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78575, d79443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d103232 q = 0) : d104033 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103232, d104033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103232, d104033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103233 q = 0) : d104034 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103233, d104034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103233, d104034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d103234 q = 0) : d104035 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103234, d104035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d103234, d104035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d103235 q = 0) : d104036 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103235, d104036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d103235, d104036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7065 (p : Pattern) (selected : d103239 p = 0) : d104040 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78574 q = 0) : d79442 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78574, d79442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4049 q selected
    | true =>
      simp only [d78574, d79442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78575 q = 0) : d79443 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78575, d79443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78575, d79443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103236 q = 0) : d104037 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103236, d104037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103236, d104037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103237 q = 0) : d104038 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103237, d104038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103237, d104038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103238 q = 0) : d104039 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103238, d104039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103238, d104039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103239 q = 0) : d104040 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103239, d104040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103239, d104040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7066 (p : Pattern) (selected : d103244 p = 0) : d104040 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78566 q = 0) : d79442 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78566, d79442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4047 q selected
    | true =>
      simp only [d78566, d79442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78567 q = 0) : d79443 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78567, d79443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78567, d79443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103241 q = 0) : d104037 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103241, d104037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103241, d104037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103242 q = 0) : d104038 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103242, d104038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103242, d104038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103243 q = 0) : d104039 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103243, d104039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103243, d104039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103244 q = 0) : d104040 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103244, d104040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103244, d104040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7067 (p : Pattern) (selected : d103247 p = 0) : d104044 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d5681 q = 0) : d74407 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5681, d74407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3395 q selected
    | true =>
      simp only [d5681, d74407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3396 q selected
  have h2 (q : Pattern) (selected : d5682 q = 0) : d74408 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5682, d74408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5682, d74408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d5683 q = 0) : d74409 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5683, d74409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5683, d74409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d5684 q = 0) : d74410 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5684, d74410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d5684, d74410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103247 q = 0) : d104044 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d103247, d104044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103247, d104044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro7068 (p : Pattern) (selected : d103253 p = 0) : d104050 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103248 q = 0) : d104045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d103248, d104045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7067 q selected
    | true =>
      simp only [d103248, d104045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d103249 q = 0) : d104046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d103249, d104046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103249, d104046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103250 q = 0) : d104047 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103250, d104047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103250, d104047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103251 q = 0) : d104048 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103251, d104048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103251, d104048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103252 q = 0) : d104049 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103252, d104049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103252, d104049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103253 q = 0) : d104050 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103253, d104050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103253, d104050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7069 (p : Pattern) (selected : d103259 p = 0) : d104056 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103240 q = 0) : d104041 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103240, d104041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7064 q selected
    | true =>
      simp only [d103240, d104041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7065 q selected
  have h2 (q : Pattern) (selected : d103245 q = 0) : d104042 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103245, d104042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7066 q selected
    | true =>
      simp only [d103245, d104042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d103246 q = 0) : d104043 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103246, d104043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103246, d104043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d103254 q = 0) : d104051 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103254, d104051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7068 q selected
    | true =>
      simp only [d103254, d104051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103255 q = 0) : d104052 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103255, d104052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103255, d104052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103256 q = 0) : d104053 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103256, d104053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103256, d104053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d103257 q = 0) : d104054 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103257, d104054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103257, d104054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d103258 q = 0) : d104055 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103258, d104055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103258, d104055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d103259 q = 0) : d104056 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d103259, d104056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103259, d104056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7070 (p : Pattern) (selected : d103265 p = 0) : d104062 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103149 q = 0) : d103957 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d103149, d103957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103149, d103957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7046 q selected
  have h2 (q : Pattern) (selected : d103150 q = 0) : d103958 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d103150, d103958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103150, d103958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d103158 q = 0) : d103966 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d103158, d103966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7046 q selected
    | true =>
      simp only [d103158, d103966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7048 q selected
  have h4 (q : Pattern) (selected : d103159 q = 0) : d103967 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d103159, d103967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103159, d103967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103160 q = 0) : d103968 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d103160, d103968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103160, d103968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103218 q = 0) : d104019 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d103218, d104019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7055 q selected
    | true =>
      simp only [d103218, d104019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7061 q selected
  have h7 (q : Pattern) (selected : d103220 q = 0) : d104021 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d103220, d104021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7062 q selected
    | true =>
      simp only [d103220, d104021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d103221 q = 0) : d104022 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d103221, d104022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d103221, d104022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d103222 q = 0) : d104023 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d103222, d104023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d103222, d104023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d103223 q = 0) : d104024 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d103223, d104024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103223, d104024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d103227 q = 0) : d104028 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d103227, d104028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103227, d104028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7063 q selected
  have h12 (q : Pattern) (selected : d103228 q = 0) : d104029 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d103228, d104029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d103228, d104029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d103229 q = 0) : d104030 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d103229, d104030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d103229, d104030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d103230 q = 0) : d104031 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d103230, d104031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d103230, d104031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d103231 q = 0) : d104032 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d103231, d104032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d103231, d104032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d103260 q = 0) : d104057 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d103260, d104057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103260, d104057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7069 q selected
  have h17 (q : Pattern) (selected : d103261 q = 0) : d104058 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d103261, d104058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d103261, d104058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d103262 q = 0) : d104059 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d103262, d104059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d103262, d104059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d103263 q = 0) : d104060 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d103263, d104060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d103263, d104060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d103264 q = 0) : d104061 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d103264, d104061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d103264, d104061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d103265 q = 0) : d104062 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d103265, d104062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d103265, d104062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro7071 (p : Pattern) (selected : d103271 p = 0) : d104068 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103266 q = 0) : d104063 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d103266, d104063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103266, d104063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7070 q selected
  have h2 (q : Pattern) (selected : d103267 q = 0) : d104064 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d103267, d104064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103267, d104064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103268 q = 0) : d104065 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d103268, d104065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103268, d104065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d103269 q = 0) : d104066 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d103269, d104066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103269, d104066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d103270 q = 0) : d104067 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d103270, d104067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103270, d104067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103271 q = 0) : d104068 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d103271, d104068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103271, d104068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7072 (p : Pattern) (selected : d103279 p = 0) : d104076 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78602 q = 0) : d79471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78602, d79471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4054 q selected
    | true =>
      simp only [d78602, d79471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78603 q = 0) : d79472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78603, d79472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78603, d79472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103276 q = 0) : d104073 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103276, d104073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103276, d104073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103277 q = 0) : d104074 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103277, d104074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103277, d104074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103278 q = 0) : d104075 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103278, d104075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103278, d104075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103279 q = 0) : d104076 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103279, d104076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103279, d104076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7073 (p : Pattern) (selected : d103285 p = 0) : d104082 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103280 q = 0) : d104077 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103280, d104077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7072 q selected
    | true =>
      simp only [d103280, d104077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d103281 q = 0) : d104078 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103281, d104078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103281, d104078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103282 q = 0) : d104079 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103282, d104079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103282, d104079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103283 q = 0) : d104080 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103283, d104080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103283, d104080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d103284 q = 0) : d104081 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103284, d104081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103284, d104081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103285 q = 0) : d104082 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d103285, d104082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103285, d104082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7074 (p : Pattern) (selected : d103288 p = 0) : d104085 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78602 q = 0) : d79471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78602, d79471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4054 q selected
    | true =>
      simp only [d78602, d79471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78603 q = 0) : d79472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78603, d79472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78603, d79472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103276 q = 0) : d104073 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103276, d104073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103276, d104073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103277 q = 0) : d104074 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103277, d104074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103277, d104074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103278 q = 0) : d104075 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103278, d104075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103278, d104075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103288 q = 0) : d104085 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103288, d104085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103288, d104085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7075 (p : Pattern) (selected : d103294 p = 0) : d104091 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103280 q = 0) : d104077 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103280, d104077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7072 q selected
    | true =>
      simp only [d103280, d104077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d103281 q = 0) : d104078 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103281, d104078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103281, d104078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103282 q = 0) : d104079 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103282, d104079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103282, d104079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103283 q = 0) : d104080 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103283, d104080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103283, d104080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d103284 q = 0) : d104081 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103284, d104081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103284, d104081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103289 q = 0) : d104086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103289, d104086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7074 q selected
    | true =>
      simp only [d103289, d104086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d103290 q = 0) : d104087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103290, d104087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103290, d104087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d103291 q = 0) : d104088 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103291, d104088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d103291, d104088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d103292 q = 0) : d104089 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103292, d104089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103292, d104089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d103293 q = 0) : d104090 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103293, d104090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103293, d104090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d103294 q = 0) : d104091 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d103294, d104091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103294, d104091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7076 (p : Pattern) (selected : d103299 p = 0) : d104096 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78602 q = 0) : d79471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78602, d79471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4054 q selected
    | true =>
      simp only [d78602, d79471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78603 q = 0) : d79472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78603, d79472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78603, d79472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103276 q = 0) : d104073 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103276, d104073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103276, d104073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103277 q = 0) : d104074 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103277, d104074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103277, d104074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103298 q = 0) : d104095 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103298, d104095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103298, d104095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103299 q = 0) : d104096 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103299, d104096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103299, d104096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7077 (p : Pattern) (selected : d103306 p = 0) : d104103 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78602 q = 0) : d79471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78602, d79471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4054 q selected
    | true =>
      simp only [d78602, d79471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78603 q = 0) : d79472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78603, d79472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78603, d79472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103276 q = 0) : d104073 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103276, d104073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103276, d104073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103304 q = 0) : d104101 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103304, d104101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103304, d104101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d103305 q = 0) : d104102 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103305, d104102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103305, d104102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103306 q = 0) : d104103 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103306, d104103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103306, d104103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7078 (p : Pattern) (selected : d103313 p = 0) : d104110 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78638 q = 0) : d79507 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78638, d79507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4061 q selected
    | true =>
      simp only [d78638, d79507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78639 q = 0) : d79508 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78639, d79508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78639, d79508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d78602 q = 0) : d79471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78602, d79471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4054 q selected
    | true =>
      simp only [d78602, d79471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d78603 q = 0) : d79472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78603, d79472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78603, d79472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d103310 q = 0) : d104107 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103310, d104107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103310, d104107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103311 q = 0) : d104108 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103311, d104108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103311, d104108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d103312 q = 0) : d104109 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103312, d104109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d103312, d104109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d103313 q = 0) : d104110 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103313, d104110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103313, d104110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7079 (p : Pattern) (selected : d103318 p = 0) : d104076 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78651 q = 0) : d79471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78651, d79471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4065 q selected
    | true =>
      simp only [d78651, d79471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78652 q = 0) : d79472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78652, d79472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78652, d79472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103315 q = 0) : d104073 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103315, d104073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103315, d104073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103316 q = 0) : d104074 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103316, d104074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103316, d104074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103317 q = 0) : d104075 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103317, d104075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103317, d104075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103318 q = 0) : d104076 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103318, d104076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103318, d104076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7080 (p : Pattern) (selected : d103321 p = 0) : d104113 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d5728 q = 0) : d74454 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5728, d74454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3403 q selected
    | true =>
      simp only [d5728, d74454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3404 q selected
  have h2 (q : Pattern) (selected : d5729 q = 0) : d74455 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5729, d74455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5729, d74455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d5730 q = 0) : d74456 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5730, d74456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5730, d74456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d5731 q = 0) : d74457 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5731, d74457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d5731, d74457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103321 q = 0) : d104113 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d103321, d104113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103321, d104113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro7081 (p : Pattern) (selected : d103327 p = 0) : d104119 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103322 q = 0) : d104114 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d103322, d104114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7080 q selected
    | true =>
      simp only [d103322, d104114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d103323 q = 0) : d104115 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d103323, d104115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103323, d104115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103324 q = 0) : d104116 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103324, d104116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103324, d104116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103325 q = 0) : d104117 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103325, d104117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103325, d104117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103326 q = 0) : d104118 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103326, d104118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103326, d104118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103327 q = 0) : d104119 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103327, d104119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103327, d104119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7082 (p : Pattern) (selected : d103333 p = 0) : d104125 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103300 q = 0) : d104097 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103300, d104097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7076 q selected
    | true =>
      simp only [d103300, d104097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d103301 q = 0) : d104098 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103301, d104098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103301, d104098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103302 q = 0) : d104099 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103302, d104099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103302, d104099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103303 q = 0) : d104100 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103303, d104100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103303, d104100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d103307 q = 0) : d104104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103307, d104104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7077 q selected
    | true =>
      simp only [d103307, d104104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103308 q = 0) : d104105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103308, d104105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103308, d104105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d103309 q = 0) : d104106 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103309, d104106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d103309, d104106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d103314 q = 0) : d104111 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103314, d104111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7078 q selected
    | true =>
      simp only [d103314, d104111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7072 q selected
  have h9 (q : Pattern) (selected : d103319 q = 0) : d104077 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103319, d104077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7079 q selected
    | true =>
      simp only [d103319, d104077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d103320 q = 0) : d104112 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103320, d104112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d103320, d104112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d103328 q = 0) : d104120 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103328, d104120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7081 q selected
    | true =>
      simp only [d103328, d104120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d103329 q = 0) : d104121 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103329, d104121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d103329, d104121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d103330 q = 0) : d104122 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103330, d104122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d103330, d104122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d103331 q = 0) : d104123 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103331, d104123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d103331, d104123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d103332 q = 0) : d104124 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103332, d104124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103332, d104124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d103333 q = 0) : d104125 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d103333, d104125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103333, d104125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro7083 (p : Pattern) (selected : d103334 p = 0) : d104126 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78602 q = 0) : d79471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78602, d79471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4054 q selected
    | true =>
      simp only [d78602, d79471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78603 q = 0) : d79472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78603, d79472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78603, d79472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103276 q = 0) : d104073 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103276, d104073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103276, d104073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103277 q = 0) : d104074 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103277, d104074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103277, d104074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103298 q = 0) : d104095 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103298, d104095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103298, d104095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103334 q = 0) : d104126 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103334, d104126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103334, d104126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7084 (p : Pattern) (selected : d103339 p = 0) : d104131 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78602 q = 0) : d79471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78602, d79471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4054 q selected
    | true =>
      simp only [d78602, d79471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78603 q = 0) : d79472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78603, d79472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78603, d79472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103276 q = 0) : d104073 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103276, d104073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103276, d104073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103304 q = 0) : d104101 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103304, d104101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103304, d104101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d103305 q = 0) : d104102 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103305, d104102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103305, d104102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103339 q = 0) : d104131 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103339, d104131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103339, d104131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7085 (p : Pattern) (selected : d103343 p = 0) : d104135 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78638 q = 0) : d79507 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78638, d79507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4061 q selected
    | true =>
      simp only [d78638, d79507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78639 q = 0) : d79508 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78639, d79508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78639, d79508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d78602 q = 0) : d79471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78602, d79471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4054 q selected
    | true =>
      simp only [d78602, d79471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d78603 q = 0) : d79472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78603, d79472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78603, d79472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d103310 q = 0) : d104107 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103310, d104107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103310, d104107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103311 q = 0) : d104108 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103311, d104108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103311, d104108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d103312 q = 0) : d104109 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103312, d104109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d103312, d104109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d103343 q = 0) : d104135 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103343, d104135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d103343, d104135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7086 (p : Pattern) (selected : d103345 p = 0) : d104085 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78651 q = 0) : d79471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78651, d79471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4065 q selected
    | true =>
      simp only [d78651, d79471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78652 q = 0) : d79472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78652, d79472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78652, d79472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103315 q = 0) : d104073 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103315, d104073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103315, d104073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103316 q = 0) : d104074 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103316, d104074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103316, d104074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103317 q = 0) : d104075 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103317, d104075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103317, d104075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103345 q = 0) : d104085 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103345, d104085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103345, d104085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7087 (p : Pattern) (selected : d103348 p = 0) : d104138 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103322 q = 0) : d104114 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d103322, d104114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7080 q selected
    | true =>
      simp only [d103322, d104114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d103323 q = 0) : d104115 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d103323, d104115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103323, d104115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103324 q = 0) : d104116 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103324, d104116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103324, d104116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103325 q = 0) : d104117 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103325, d104117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103325, d104117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103326 q = 0) : d104118 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103326, d104118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103326, d104118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103348 q = 0) : d104138 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103348, d104138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103348, d104138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7088 (p : Pattern) (selected : d103354 p = 0) : d104144 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103300 q = 0) : d104097 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103300, d104097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7076 q selected
    | true =>
      simp only [d103300, d104097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d103301 q = 0) : d104098 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103301, d104098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103301, d104098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103302 q = 0) : d104099 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103302, d104099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103302, d104099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103303 q = 0) : d104100 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103303, d104100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103303, d104100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d103307 q = 0) : d104104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103307, d104104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7077 q selected
    | true =>
      simp only [d103307, d104104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103308 q = 0) : d104105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103308, d104105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103308, d104105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d103309 q = 0) : d104106 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103309, d104106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d103309, d104106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d103314 q = 0) : d104111 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103314, d104111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7078 q selected
    | true =>
      simp only [d103314, d104111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7072 q selected
  have h9 (q : Pattern) (selected : d103319 q = 0) : d104077 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103319, d104077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7079 q selected
    | true =>
      simp only [d103319, d104077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d103320 q = 0) : d104112 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103320, d104112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d103320, d104112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d103328 q = 0) : d104120 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103328, d104120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7081 q selected
    | true =>
      simp only [d103328, d104120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d103329 q = 0) : d104121 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103329, d104121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d103329, d104121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d103330 q = 0) : d104122 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103330, d104122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d103330, d104122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d103331 q = 0) : d104123 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103331, d104123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d103331, d104123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d103332 q = 0) : d104124 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103332, d104124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103332, d104124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d103335 q = 0) : d104127 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103335, d104127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7083 q selected
    | true =>
      simp only [d103335, d104127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d103336 q = 0) : d104128 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103336, d104128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103336, d104128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d103337 q = 0) : d104129 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103337, d104129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d103337, d104129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d103338 q = 0) : d104130 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103338, d104130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103338, d104130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d103340 q = 0) : d104132 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103340, d104132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7084 q selected
    | true =>
      simp only [d103340, d104132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d103341 q = 0) : d104133 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103341, d104133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103341, d104133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d103342 q = 0) : d104134 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103342, d104134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d103342, d104134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d103344 q = 0) : d104136 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103344, d104136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7085 q selected
    | true =>
      simp only [d103344, d104136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7074 q selected
  have h24 (q : Pattern) (selected : d103346 q = 0) : d104086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103346, d104086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7086 q selected
    | true =>
      simp only [d103346, d104086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d103347 q = 0) : d104137 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103347, d104137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d103347, d104137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d103349 q = 0) : d104139 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103349, d104139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7087 q selected
    | true =>
      simp only [d103349, d104139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d103350 q = 0) : d104140 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103350, d104140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d103350, d104140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d103351 q = 0) : d104141 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103351, d104141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d103351, d104141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d103352 q = 0) : d104142 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103352, d104142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d103352, d104142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d103353 q = 0) : d104143 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103353, d104143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d103353, d104143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d103354 q = 0) : d104144 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d103354, d104144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d103354, d104144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro7089 (p : Pattern) (selected : d103356 p = 0) : d104146 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103280 q = 0) : d104077 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103280, d104077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7072 q selected
    | true =>
      simp only [d103280, d104077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d103281 q = 0) : d104078 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103281, d104078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103281, d104078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103282 q = 0) : d104079 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103282, d104079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103282, d104079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103283 q = 0) : d104080 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103283, d104080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103283, d104080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d103284 q = 0) : d104081 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103284, d104081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103284, d104081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103356 q = 0) : d104146 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d103356, d104146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103356, d104146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7090 (p : Pattern) (selected : d103363 p = 0) : d104153 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103344 q = 0) : d104136 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103344, d104136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7085 q selected
    | true =>
      simp only [d103344, d104136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7074 q selected
  have h2 (q : Pattern) (selected : d103346 q = 0) : d104086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103346, d104086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7086 q selected
    | true =>
      simp only [d103346, d104086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d103347 q = 0) : d104137 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103347, d104137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103347, d104137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d103349 q = 0) : d104139 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103349, d104139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7087 q selected
    | true =>
      simp only [d103349, d104139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103350 q = 0) : d104140 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103350, d104140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103350, d104140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103351 q = 0) : d104141 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103351, d104141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103351, d104141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d103361 q = 0) : d104151 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103361, d104151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103361, d104151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d103362 q = 0) : d104152 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103362, d104152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103362, d104152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d103363 q = 0) : d104153 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d103363, d104153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103363, d104153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7091 (p : Pattern) (selected : d103372 p = 0) : d104162 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78703 q = 0) : d79563 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78703, d79563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4076 q selected
    | true =>
      simp only [d78703, d79563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78704 q = 0) : d79564 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78704, d79564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78704, d79564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d78724 q = 0) : d79576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78724, d79576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4082 q selected
    | true =>
      simp only [d78724, d79576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d78725 q = 0) : d79577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78725, d79577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78725, d79577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d103369 q = 0) : d104159 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103369, d104159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103369, d104159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103370 q = 0) : d104160 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103370, d104160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103370, d104160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d103371 q = 0) : d104161 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103371, d104161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d103371, d104161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d103372 q = 0) : d104162 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103372, d104162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d103372, d104162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7092 (p : Pattern) (selected : d103376 p = 0) : d104166 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78724 q = 0) : d79576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78724, d79576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4082 q selected
    | true =>
      simp only [d78724, d79576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78725 q = 0) : d79577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78725, d79577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78725, d79577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103373 q = 0) : d104163 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103373, d104163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103373, d104163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103374 q = 0) : d104164 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103374, d104164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103374, d104164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103375 q = 0) : d104165 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103375, d104165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103375, d104165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103376 q = 0) : d104166 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103376, d104166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103376, d104166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7093 (p : Pattern) (selected : d103381 p = 0) : d104166 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78716 q = 0) : d79576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78716, d79576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4080 q selected
    | true =>
      simp only [d78716, d79576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78717 q = 0) : d79577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78717, d79577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78717, d79577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103378 q = 0) : d104163 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103378, d104163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103378, d104163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103379 q = 0) : d104164 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103379, d104164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103379, d104164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103380 q = 0) : d104165 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103380, d104165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103380, d104165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103381 q = 0) : d104166 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103381, d104166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103381, d104166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7094 (p : Pattern) (selected : d103384 p = 0) : d104170 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d5772 q = 0) : d74498 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5772, d74498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3411 q selected
    | true =>
      simp only [d5772, d74498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3412 q selected
  have h2 (q : Pattern) (selected : d5773 q = 0) : d74499 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5773, d74499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5773, d74499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d5774 q = 0) : d74500 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5774, d74500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5774, d74500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d5775 q = 0) : d74501 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5775, d74501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d5775, d74501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103384 q = 0) : d104170 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d103384, d104170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103384, d104170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro7095 (p : Pattern) (selected : d103390 p = 0) : d104176 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103385 q = 0) : d104171 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d103385, d104171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7094 q selected
    | true =>
      simp only [d103385, d104171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d103386 q = 0) : d104172 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d103386, d104172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103386, d104172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103387 q = 0) : d104173 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103387, d104173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103387, d104173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103388 q = 0) : d104174 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103388, d104174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103388, d104174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103389 q = 0) : d104175 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103389, d104175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103389, d104175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103390 q = 0) : d104176 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103390, d104176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103390, d104176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7096 (p : Pattern) (selected : d103396 p = 0) : d104182 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103377 q = 0) : d104167 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103377, d104167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7091 q selected
    | true =>
      simp only [d103377, d104167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7092 q selected
  have h2 (q : Pattern) (selected : d103382 q = 0) : d104168 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103382, d104168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7093 q selected
    | true =>
      simp only [d103382, d104168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d103383 q = 0) : d104169 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103383, d104169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103383, d104169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d103391 q = 0) : d104177 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103391, d104177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7095 q selected
    | true =>
      simp only [d103391, d104177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103392 q = 0) : d104178 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103392, d104178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103392, d104178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103393 q = 0) : d104179 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103393, d104179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103393, d104179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d103394 q = 0) : d104180 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103394, d104180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103394, d104180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d103395 q = 0) : d104181 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103395, d104181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103395, d104181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d103396 q = 0) : d104182 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d103396, d104182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103396, d104182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7097 (p : Pattern) (selected : d103402 p = 0) : d104188 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103286 q = 0) : d104083 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d103286, d104083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103286, d104083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7073 q selected
  have h2 (q : Pattern) (selected : d103287 q = 0) : d104084 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d103287, d104084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103287, d104084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d103295 q = 0) : d104092 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d103295, d104092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7073 q selected
    | true =>
      simp only [d103295, d104092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7075 q selected
  have h4 (q : Pattern) (selected : d103296 q = 0) : d104093 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d103296, d104093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103296, d104093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103297 q = 0) : d104094 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d103297, d104094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103297, d104094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103355 q = 0) : d104145 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d103355, d104145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7082 q selected
    | true =>
      simp only [d103355, d104145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7088 q selected
  have h7 (q : Pattern) (selected : d103357 q = 0) : d104147 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d103357, d104147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7089 q selected
    | true =>
      simp only [d103357, d104147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d103358 q = 0) : d104148 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d103358, d104148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d103358, d104148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d103359 q = 0) : d104149 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d103359, d104149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d103359, d104149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d103360 q = 0) : d104150 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d103360, d104150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103360, d104150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d103364 q = 0) : d104154 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d103364, d104154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103364, d104154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7090 q selected
  have h12 (q : Pattern) (selected : d103365 q = 0) : d104155 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d103365, d104155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d103365, d104155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d103366 q = 0) : d104156 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d103366, d104156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d103366, d104156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d103367 q = 0) : d104157 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d103367, d104157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d103367, d104157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d103368 q = 0) : d104158 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d103368, d104158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d103368, d104158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d103397 q = 0) : d104183 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d103397, d104183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103397, d104183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7096 q selected
  have h17 (q : Pattern) (selected : d103398 q = 0) : d104184 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d103398, d104184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d103398, d104184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d103399 q = 0) : d104185 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d103399, d104185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d103399, d104185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d103400 q = 0) : d104186 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d103400, d104186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d103400, d104186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d103401 q = 0) : d104187 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d103401, d104187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d103401, d104187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d103402 q = 0) : d104188 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d103402, d104188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d103402, d104188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro7098 (p : Pattern) (selected : d103408 p = 0) : d104194 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103403 q = 0) : d104189 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d103403, d104189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103403, d104189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7097 q selected
  have h2 (q : Pattern) (selected : d103404 q = 0) : d104190 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d103404, d104190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103404, d104190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103405 q = 0) : d104191 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d103405, d104191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103405, d104191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d103406 q = 0) : d104192 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d103406, d104192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103406, d104192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d103407 q = 0) : d104193 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d103407, d104193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103407, d104193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103408 q = 0) : d104194 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d103408, d104194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103408, d104194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7099 (p : Pattern) (selected : d103414 p = 0) : d104200 p = 1 := by
  have h0 (q : Pattern) (selected : d102867 q = 0) : d103697 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d102867, d103697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6968 q selected
    | true =>
      simp only [d102867, d103697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6990 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d103001 q = 0) : d103820 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d103001, d103820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103001, d103820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7017 q selected
  have h3 (q : Pattern) (selected : d103002 q = 0) : d103821 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d103002, d103821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103002, d103821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d103136 q = 0) : d103944 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d103136, d103944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103136, d103944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7044 q selected
  have h5 (q : Pattern) (selected : d103137 q = 0) : d103945 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d103137, d103945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103137, d103945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103138 q = 0) : d103946 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d103138, d103946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103138, d103946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d103272 q = 0) : d104069 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d103272, d104069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103272, d104069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7071 q selected
  have h8 (q : Pattern) (selected : d103273 q = 0) : d104070 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d103273, d104070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103273, d104070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d103274 q = 0) : d104071 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d103274, d104071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103274, d104071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d103275 q = 0) : d104072 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d103275, d104072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d103275, d104072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d103409 q = 0) : d104195 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d103409, d104195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103409, d104195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7098 q selected
  have h12 (q : Pattern) (selected : d103410 q = 0) : d104196 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d103410, d104196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103410, d104196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d103411 q = 0) : d104197 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d103411, d104197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103411, d104197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d103412 q = 0) : d104198 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d103412, d104198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103412, d104198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d103413 q = 0) : d104199 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d103413, d104199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d103413, d104199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d103414 q = 0) : d104200 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d103414, d104200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d103414, d104200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro7100 (p : Pattern) (selected : d103420 p = 0) : d104206 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103415 q = 0) : d104201 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d103415, d104201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7099 q selected
    | true =>
      simp only [d103415, d104201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d103416 q = 0) : d104202 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d103416, d104202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103416, d104202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d103417 q = 0) : d104203 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d103417, d104203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103417, d104203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103418 q = 0) : d104204 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d103418, d104204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103418, d104204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103419 q = 0) : d104205 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d103419, d104205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103419, d104205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103420 q = 0) : d104206 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d103420, d104206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103420, d104206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7101 (p : Pattern) (selected : d103426 p = 0) : d104212 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103421 q = 0) : d104207 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d103421, d104207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7100 q selected
    | true =>
      simp only [d103421, d104207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d103422 q = 0) : d104208 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d103422, d104208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103422, d104208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d103423 q = 0) : d104209 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d103423, d104209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103423, d104209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103424 q = 0) : d104210 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d103424, d104210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103424, d104210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103425 q = 0) : d104211 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d103425, d104211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103425, d104211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103426 q = 0) : d104212 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d103426, d104212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103426, d104212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7102 (p : Pattern) (selected : d103432 p = 0) : d104218 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103427 q = 0) : d104213 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d103427, d104213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7101 q selected
    | true =>
      simp only [d103427, d104213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d103428 q = 0) : d104214 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d103428, d104214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103428, d104214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d103429 q = 0) : d104215 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d103429, d104215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103429, d104215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103430 q = 0) : d104216 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d103430, d104216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103430, d104216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103431 q = 0) : d104217 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d103431, d104217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103431, d104217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103432 q = 0) : d104218 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d103432, d104218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103432, d104218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7103 (p : Pattern) (selected : d103437 p = 0) : d104223 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103433 q = 0) : d104219 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d103433, d104219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7102 q selected
    | true =>
      simp only [d103433, d104219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d103434 q = 0) : d104220 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d103434, d104220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103434, d104220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d103435 q = 0) : d104221 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d103435, d104221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103435, d104221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103436 q = 0) : d104222 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d103436, d104222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103436, d104222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103437 q = 0) : d104223 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d103437, d104223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103437, d104223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro7104 (p : Pattern) (selected : d103443 p = 0) : d104229 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103438 q = 0) : d104224 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d103438, d104224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7103 q selected
    | true =>
      simp only [d103438, d104224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d103439 q = 0) : d104225 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d103439, d104225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103439, d104225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d103440 q = 0) : d104226 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d103440, d104226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103440, d104226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103441 q = 0) : d104227 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d103441, d104227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103441, d104227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103442 q = 0) : d104228 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d103442, d104228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103442, d104228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103443 q = 0) : d104229 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d103443, d104229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103443, d104229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7105 (p : Pattern) (selected : d103449 p = 0) : d104235 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103444 q = 0) : d104230 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d103444, d104230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7104 q selected
    | true =>
      simp only [d103444, d104230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d103445 q = 0) : d104231 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d103445, d104231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103445, d104231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d103446 q = 0) : d104232 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d103446, d104232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103446, d104232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103447 q = 0) : d104233 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d103447, d104233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103447, d104233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103448 q = 0) : d104234 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d103448, d104234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103448, d104234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103449 q = 0) : d104235 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d103449, d104235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103449, d104235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7106 (p : Pattern) (selected : d103455 p = 0) : d104241 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d103450 q = 0) : d104236 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d103450, d104236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7105 q selected
    | true =>
      simp only [d103450, d104236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d103451 q = 0) : d104237 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d103451, d104237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103451, d104237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d103452 q = 0) : d104238 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d103452, d104238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103452, d104238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103453 q = 0) : d104239 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d103453, d104239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103453, d104239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103454 q = 0) : d104240 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d103454, d104240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103454, d104240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103455 q = 0) : d104241 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d103455, d104241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103455, d104241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7107 (p : Pattern) (selected : d102685 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d77933 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d77933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4095 q selected
    | true =>
      simp only [d77933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d77934 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d77934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d77934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d102682 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d102682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d102682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d102683 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d102683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d102683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d102684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d102684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d102684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d102685 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d102685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7108 (p : Pattern) (selected : d102691 p = 1) : d104246 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d102670 q = 1) : d102670 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d102676 q = 1) : d102676 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d102681 q = 1) : d102681 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d102686 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d102686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7107 q selected
    | true =>
      simp only [d102686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d102687 q = 1) : d104242 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d102687, d104242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d102687, d104242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d102607 q = 1) : d102607 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d102688 q = 1) : d104243 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d102688, d104243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d102688, d104243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d102689 q = 1) : d104244 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102689, d104244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d102689, d104244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d102690 q = 1) : d104245 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d102690, d104245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d102690, d104245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d102691 q = 1) : d104246 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d102691, d104246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102691, d104246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro7109 (p : Pattern) (selected : d102703 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d77933 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d77933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4095 q selected
    | true =>
      simp only [d77933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d77934 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d77934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d77934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d102682 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d102682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d102682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d102683 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d102683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d102683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d102684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d102684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d102684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d102703 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d102703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d102703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7110 (p : Pattern) (selected : d102709 p = 1) : d104251 p = 1 := by
  have h0 (q : Pattern) (selected : d102670 q = 1) : d102670 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d102676 q = 1) : d102676 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d102681 q = 1) : d102681 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d102686 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d102686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7107 q selected
    | true =>
      simp only [d102686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d102687 q = 1) : d104242 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d102687, d104242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d102687, d104242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d102607 q = 1) : d102607 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d102688 q = 1) : d104243 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d102688, d104243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d102688, d104243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d102689 q = 1) : d104244 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102689, d104244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d102689, d104244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d102690 q = 1) : d104245 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d102690, d104245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102690, d104245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d102696 q = 1) : d102696 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d102700 q = 1) : d102700 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d102702 q = 1) : d102702 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d102704 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d102704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7109 q selected
    | true =>
      simp only [d102704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d102705 q = 1) : d104247 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d102705, d104247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d102705, d104247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d102614 q = 1) : d102614 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d102706 q = 1) : d104248 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d102706, d104248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d102706, d104248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d102707 q = 1) : d104249 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102707, d104249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d102707, d104249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d102708 q = 1) : d104250 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d102708, d104250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d102708, d104250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d102709 q = 1) : d104251 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d102709, d104251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d102709, d104251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro7111 (p : Pattern) (selected : d102718 p = 1) : d104258 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d102702 q = 1) : d102702 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d102704 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d102704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7109 q selected
    | true =>
      simp only [d102704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d102705 q = 1) : d104247 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d102705, d104247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d102705, d104247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d102614 q = 1) : d102614 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d102706 q = 1) : d104248 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d102706, d104248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d102706, d104248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d102716 q = 1) : d104256 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102716, d104256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102716, d104256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d102717 q = 1) : d104257 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d102717, d104257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102717, d104257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d102718 q = 1) : d104258 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d102718, d104258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102718, d104258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7112 (p : Pattern) (selected : d102732 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d77984 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d77984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4101 q selected
    | true =>
      simp only [d77984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d77985 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d77985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d77985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d102729 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d102729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d102729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d102730 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d102730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d102730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d102731 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d102731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d102731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d102732 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d102732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d102732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7113 (p : Pattern) (selected : d102738 p = 1) : d104268 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d102728 q = 1) : d102728 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d102733 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d102733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7112 q selected
    | true =>
      simp only [d102733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d102734 q = 1) : d104264 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d102734, d104264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d102734, d104264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d102634 q = 1) : d102634 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d102735 q = 1) : d104265 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d102735, d104265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d102735, d104265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d102736 q = 1) : d104266 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102736, d104266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102736, d104266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d102737 q = 1) : d104267 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d102737, d104267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102737, d104267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d102738 q = 1) : d104268 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d102738, d104268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102738, d104268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7114 (p : Pattern) (selected : d102744 p = 1) : d104274 p = 1 := by
  have h0 (q : Pattern) (selected : d102664 q = 1) : d102664 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d102710 q = 1) : d104252 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d102710, d104252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7108 q selected
    | true =>
      simp only [d102710, d104252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7110 q selected
  have h2 (q : Pattern) (selected : d102712 q = 1) : d102712 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d102713 q = 1) : d104253 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d102713, d104253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d102713, d104253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d102714 q = 1) : d104254 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d102714, d104254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d102714, d104254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d102715 q = 1) : d104255 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d102715, d104255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102715, d104255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d102719 q = 1) : d104259 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d102719, d104259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d102719, d104259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7111 q selected
  have h8 (q : Pattern) (selected : d102720 q = 1) : d104260 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d102720, d104260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d102720, d104260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d102721 q = 1) : d104261 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d102721, d104261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d102721, d104261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d102722 q = 1) : d104262 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d102722, d104262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d102722, d104262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d102723 q = 1) : d104263 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d102723, d104263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d102723, d104263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d102739 q = 1) : d104269 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d102739, d104269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d102739, d104269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7113 q selected
  have h13 (q : Pattern) (selected : d102740 q = 1) : d104270 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d102740, d104270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d102740, d104270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d102741 q = 1) : d104271 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d102741, d104271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d102741, d104271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d102742 q = 1) : d104272 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d102742, d104272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d102742, d104272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d102743 q = 1) : d104273 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d102743, d104273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d102743, d104273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d102744 q = 1) : d104274 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d102744, d104274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d102744, d104274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro7115 (p : Pattern) (selected : d102750 p = 1) : d104280 p = 1 := by
  have h0 (q : Pattern) (selected : d102649 q = 1) : d102649 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d102745 q = 1) : d104275 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d102745, d104275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d102745, d104275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7114 q selected
  have h3 (q : Pattern) (selected : d102746 q = 1) : d104276 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d102746, d104276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d102746, d104276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d102747 q = 1) : d104277 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d102747, d104277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d102747, d104277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d102748 q = 1) : d104278 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d102748, d104278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d102748, d104278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d102749 q = 1) : d104279 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d102749, d104279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d102749, d104279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d102750 q = 1) : d104280 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d102750, d104280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102750, d104280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro7116 (p : Pattern) (selected : d102793 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d78057 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4106 q selected
    | true =>
      simp only [d78057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78058 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d102790 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d102790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d102790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d102791 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d102791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d102791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d102792 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d102792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d102792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d102793 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d102793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7117 (p : Pattern) (selected : d102800 p = 1) : d104285 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d102778 q = 1) : d102778 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d102784 q = 1) : d102784 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d102789 q = 1) : d102789 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d102794 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d102794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7116 q selected
    | true =>
      simp only [d102794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d102795 q = 1) : d104281 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d102795, d104281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d102795, d104281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d102796 q = 1) : d102796 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d102797 q = 1) : d104282 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d102797, d104282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d102797, d104282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d102798 q = 1) : d104283 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102798, d104283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d102798, d104283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d102799 q = 1) : d104284 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d102799, d104284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d102799, d104284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d102800 q = 1) : d104285 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d102800, d104285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102800, d104285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro7118 (p : Pattern) (selected : d102812 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d78057 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4106 q selected
    | true =>
      simp only [d78057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78058 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d102790 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d102790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d102790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d102791 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d102791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d102791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d102792 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d102792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d102792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d102812 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d102812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d102812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7119 (p : Pattern) (selected : d102819 p = 1) : d104290 p = 1 := by
  have h0 (q : Pattern) (selected : d102778 q = 1) : d102778 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d102784 q = 1) : d102784 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d102789 q = 1) : d102789 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d102794 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d102794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7116 q selected
    | true =>
      simp only [d102794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d102795 q = 1) : d104281 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d102795, d104281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d102795, d104281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d102796 q = 1) : d102796 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d102797 q = 1) : d104282 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d102797, d104282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d102797, d104282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d102798 q = 1) : d104283 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102798, d104283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d102798, d104283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d102799 q = 1) : d104284 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d102799, d104284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102799, d104284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d102805 q = 1) : d102805 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d102809 q = 1) : d102809 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d102811 q = 1) : d102811 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d102813 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d102813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7118 q selected
    | true =>
      simp only [d102813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d102814 q = 1) : d104286 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d102814, d104286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d102814, d104286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d102815 q = 1) : d102815 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d102816 q = 1) : d104287 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d102816, d104287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d102816, d104287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d102817 q = 1) : d104288 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102817, d104288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d102817, d104288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d102818 q = 1) : d104289 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d102818, d104289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d102818, d104289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d102819 q = 1) : d104290 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d102819, d104290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d102819, d104290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro7120 (p : Pattern) (selected : d102828 p = 1) : d104297 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d102811 q = 1) : d102811 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d102813 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d102813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7118 q selected
    | true =>
      simp only [d102813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d102814 q = 1) : d104286 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d102814, d104286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d102814, d104286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d102815 q = 1) : d102815 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d102816 q = 1) : d104287 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d102816, d104287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d102816, d104287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d102826 q = 1) : d104295 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102826, d104295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102826, d104295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d102827 q = 1) : d104296 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d102827, d104296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102827, d104296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d102828 q = 1) : d104297 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d102828, d104297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102828, d104297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7121 (p : Pattern) (selected : d102846 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d78122 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4112 q selected
    | true =>
      simp only [d78122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78123 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d102843 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d102843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d102843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d102844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d102844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d102844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d102845 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d102845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d102845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d102846 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d102846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d102846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7122 (p : Pattern) (selected : d102854 p = 1) : d104307 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d102842 q = 1) : d102842 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d102847 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d102847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7121 q selected
    | true =>
      simp only [d102847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d102848 q = 1) : d104303 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d102848, d104303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d102848, d104303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d102850 q = 1) : d102850 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d102851 q = 1) : d104304 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d102851, d104304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d102851, d104304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d102852 q = 1) : d104305 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102852, d104305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102852, d104305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d102853 q = 1) : d104306 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d102853, d104306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102853, d104306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d102854 q = 1) : d104307 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d102854, d104307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102854, d104307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7123 (p : Pattern) (selected : d102860 p = 1) : d104313 p = 1 := by
  have h0 (q : Pattern) (selected : d102772 q = 1) : d102772 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d102820 q = 1) : d104291 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d102820, d104291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7117 q selected
    | true =>
      simp only [d102820, d104291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7119 q selected
  have h2 (q : Pattern) (selected : d102822 q = 1) : d102822 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d102823 q = 1) : d104292 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d102823, d104292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d102823, d104292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d102824 q = 1) : d104293 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d102824, d104293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d102824, d104293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d102825 q = 1) : d104294 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d102825, d104294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102825, d104294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d102829 q = 1) : d104298 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d102829, d104298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d102829, d104298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7120 q selected
  have h8 (q : Pattern) (selected : d102830 q = 1) : d104299 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d102830, d104299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d102830, d104299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d102831 q = 1) : d104300 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d102831, d104300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d102831, d104300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d102832 q = 1) : d104301 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d102832, d104301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d102832, d104301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d102833 q = 1) : d104302 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d102833, d104302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d102833, d104302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d102855 q = 1) : d104308 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d102855, d104308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d102855, d104308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7122 q selected
  have h13 (q : Pattern) (selected : d102856 q = 1) : d104309 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d102856, d104309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d102856, d104309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d102857 q = 1) : d104310 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d102857, d104310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d102857, d104310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d102858 q = 1) : d104311 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d102858, d104311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d102858, d104311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d102859 q = 1) : d104312 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d102859, d104312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d102859, d104312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d102860 q = 1) : d104313 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d102860, d104313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d102860, d104313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro7124 (p : Pattern) (selected : d102866 p = 1) : d104319 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d102861 q = 1) : d104314 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d102861, d104314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102861, d104314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7123 q selected
  have h2 (q : Pattern) (selected : d102862 q = 1) : d104315 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d102862, d104315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102862, d104315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d102863 q = 1) : d104316 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d102863, d104316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102863, d104316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d102864 q = 1) : d104317 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d102864, d104317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102864, d104317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d102865 q = 1) : d104318 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d102865, d104318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102865, d104318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d102866 q = 1) : d104319 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d102866, d104319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102866, d104319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7125 (p : Pattern) (selected : d102910 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d78204 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4117 q selected
    | true =>
      simp only [d78204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78205 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d102907 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d102907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d102907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d102908 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d102908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d102908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d102909 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d102909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d102909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d102910 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d102910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7126 (p : Pattern) (selected : d102925 p = 1) : d104325 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d102895 q = 1) : d102895 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d102901 q = 1) : d102901 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d102906 q = 1) : d102906 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d102911 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d102911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7125 q selected
    | true =>
      simp only [d102911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d102912 q = 1) : d104321 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d102912, d104321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d102912, d104321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d102921 q = 1) : d102921 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d102922 q = 1) : d104322 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d102922, d104322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d102922, d104322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d102923 q = 1) : d104323 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102923, d104323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d102923, d104323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d102924 q = 1) : d104324 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d102924, d104324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d102924, d104324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d102925 q = 1) : d104325 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d102925, d104325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102925, d104325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro7127 (p : Pattern) (selected : d102937 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d78204 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4117 q selected
    | true =>
      simp only [d78204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78205 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d102907 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d102907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d102907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d102908 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d102908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d102908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d102909 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d102909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d102909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d102937 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d102937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d102937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7128 (p : Pattern) (selected : d102946 p = 1) : d104330 p = 1 := by
  have h0 (q : Pattern) (selected : d102895 q = 1) : d102895 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d102901 q = 1) : d102901 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d102906 q = 1) : d102906 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d102911 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d102911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7125 q selected
    | true =>
      simp only [d102911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d102912 q = 1) : d104321 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d102912, d104321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d102912, d104321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d102921 q = 1) : d102921 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d102922 q = 1) : d104322 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d102922, d104322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d102922, d104322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d102923 q = 1) : d104323 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102923, d104323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d102923, d104323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d102924 q = 1) : d104324 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d102924, d104324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102924, d104324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d102930 q = 1) : d102930 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d102934 q = 1) : d102934 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d102936 q = 1) : d102936 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d102938 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d102938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7127 q selected
    | true =>
      simp only [d102938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d102939 q = 1) : d104326 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d102939, d104326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d102939, d104326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d102942 q = 1) : d102942 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d102943 q = 1) : d104327 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d102943, d104327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d102943, d104327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d102944 q = 1) : d104328 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102944, d104328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d102944, d104328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d102945 q = 1) : d104329 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d102945, d104329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d102945, d104329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d102946 q = 1) : d104330 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d102946, d104330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d102946, d104330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro7129 (p : Pattern) (selected : d102955 p = 1) : d104337 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d102936 q = 1) : d102936 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d102938 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d102938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7127 q selected
    | true =>
      simp only [d102938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d102939 q = 1) : d104326 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d102939, d104326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d102939, d104326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d102942 q = 1) : d102942 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d102943 q = 1) : d104327 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d102943, d104327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d102943, d104327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d102953 q = 1) : d104335 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102953, d104335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102953, d104335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d102954 q = 1) : d104336 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d102954, d104336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102954, d104336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d102955 q = 1) : d104337 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d102955, d104337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102955, d104337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7130 (p : Pattern) (selected : d102973 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d78269 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4123 q selected
    | true =>
      simp only [d78269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78270 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d102970 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d102970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d102970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d102971 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d102971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d102971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d102972 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d102972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d102972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d102973 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d102973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d102973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7131 (p : Pattern) (selected : d102988 p = 1) : d104347 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d102969 q = 1) : d102969 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d102974 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d102974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7130 q selected
    | true =>
      simp only [d102974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d102975 q = 1) : d104343 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d102975, d104343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d102975, d104343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d102984 q = 1) : d102984 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d102985 q = 1) : d104344 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d102985, d104344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d102985, d104344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d102986 q = 1) : d104345 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102986, d104345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102986, d104345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d102987 q = 1) : d104346 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d102987, d104346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102987, d104346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d102988 q = 1) : d104347 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d102988, d104347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102988, d104347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7132 (p : Pattern) (selected : d102994 p = 1) : d104353 p = 1 := by
  have h0 (q : Pattern) (selected : d102889 q = 1) : d102889 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d102947 q = 1) : d104331 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d102947, d104331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7126 q selected
    | true =>
      simp only [d102947, d104331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7128 q selected
  have h2 (q : Pattern) (selected : d102949 q = 1) : d102949 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d102950 q = 1) : d104332 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d102950, d104332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d102950, d104332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d102951 q = 1) : d104333 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d102951, d104333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d102951, d104333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d102952 q = 1) : d104334 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d102952, d104334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102952, d104334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d102956 q = 1) : d104338 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d102956, d104338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d102956, d104338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7129 q selected
  have h8 (q : Pattern) (selected : d102957 q = 1) : d104339 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d102957, d104339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d102957, d104339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d102958 q = 1) : d104340 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d102958, d104340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d102958, d104340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d102959 q = 1) : d104341 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d102959, d104341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d102959, d104341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d102960 q = 1) : d104342 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d102960, d104342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d102960, d104342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d102989 q = 1) : d104348 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d102989, d104348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d102989, d104348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7131 q selected
  have h13 (q : Pattern) (selected : d102990 q = 1) : d104349 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d102990, d104349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d102990, d104349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d102991 q = 1) : d104350 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d102991, d104350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d102991, d104350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d102992 q = 1) : d104351 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d102992, d104351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d102992, d104351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d102993 q = 1) : d104352 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d102993, d104352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d102993, d104352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d102994 q = 1) : d104353 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d102994, d104353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d102994, d104353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro7133 (p : Pattern) (selected : d103000 p = 1) : d104359 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d102995 q = 1) : d104354 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d102995, d104354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102995, d104354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7132 q selected
  have h2 (q : Pattern) (selected : d102996 q = 1) : d104355 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d102996, d104355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102996, d104355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d102997 q = 1) : d104356 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d102997, d104356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102997, d104356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d102998 q = 1) : d104357 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d102998, d104357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102998, d104357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d102999 q = 1) : d104358 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d102999, d104358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102999, d104358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103000 q = 1) : d104359 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d103000, d104359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103000, d104359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7134 (p : Pattern) (selected : d103045 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d78352 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4128 q selected
    | true =>
      simp only [d78352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78353 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103042 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103043 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103045 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7135 (p : Pattern) (selected : d103060 p = 1) : d104366 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d103030 q = 1) : d103030 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d103036 q = 1) : d103036 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d103041 q = 1) : d103041 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d103046 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7134 q selected
    | true =>
      simp only [d103046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103047 q = 1) : d104362 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103047, d104362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103047, d104362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103056 q = 1) : d103056 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d103057 q = 1) : d104363 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103057, d104363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103057, d104363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d103058 q = 1) : d104364 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103058, d104364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103058, d104364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d103059 q = 1) : d104365 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103059, d104365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103059, d104365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d103060 q = 1) : d104366 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d103060, d104366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103060, d104366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro7136 (p : Pattern) (selected : d103072 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d78352 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4128 q selected
    | true =>
      simp only [d78352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78353 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103042 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103043 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103072 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7137 (p : Pattern) (selected : d103081 p = 1) : d104371 p = 1 := by
  have h0 (q : Pattern) (selected : d103030 q = 1) : d103030 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d103036 q = 1) : d103036 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d103041 q = 1) : d103041 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d103046 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7134 q selected
    | true =>
      simp only [d103046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d103047 q = 1) : d104362 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103047, d104362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103047, d104362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103056 q = 1) : d103056 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d103057 q = 1) : d104363 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103057, d104363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103057, d104363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d103058 q = 1) : d104364 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103058, d104364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103058, d104364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d103059 q = 1) : d104365 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103059, d104365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103059, d104365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d103065 q = 1) : d103065 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d103069 q = 1) : d103069 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d103071 q = 1) : d103071 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d103073 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7136 q selected
    | true =>
      simp only [d103073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d103074 q = 1) : d104367 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103074, d104367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d103074, d104367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d103077 q = 1) : d103077 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d103078 q = 1) : d104368 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103078, d104368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d103078, d104368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d103079 q = 1) : d104369 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103079, d104369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d103079, d104369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d103080 q = 1) : d104370 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103080, d104370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d103080, d104370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d103081 q = 1) : d104371 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d103081, d104371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d103081, d104371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro7138 (p : Pattern) (selected : d103090 p = 1) : d104378 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d103071 q = 1) : d103071 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d103073 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7136 q selected
    | true =>
      simp only [d103073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d103074 q = 1) : d104367 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103074, d104367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103074, d104367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d103077 q = 1) : d103077 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d103078 q = 1) : d104368 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103078, d104368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103078, d104368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103088 q = 1) : d104376 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103088, d104376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103088, d104376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d103089 q = 1) : d104377 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103089, d104377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103089, d104377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d103090 q = 1) : d104378 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d103090, d104378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103090, d104378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7139 (p : Pattern) (selected : d103108 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d78417 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4134 q selected
    | true =>
      simp only [d78417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78418 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103105 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103106 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103107 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103108 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7140 (p : Pattern) (selected : d103123 p = 1) : d104388 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d103104 q = 1) : d103104 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d103109 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7139 q selected
    | true =>
      simp only [d103109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d103110 q = 1) : d104384 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103110, d104384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103110, d104384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d103119 q = 1) : d103119 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d103120 q = 1) : d104385 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103120, d104385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103120, d104385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103121 q = 1) : d104386 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103121, d104386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103121, d104386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d103122 q = 1) : d104387 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103122, d104387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103122, d104387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d103123 q = 1) : d104388 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d103123, d104388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103123, d104388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7141 (p : Pattern) (selected : d103129 p = 1) : d104394 p = 1 := by
  have h0 (q : Pattern) (selected : d103024 q = 1) : d103024 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d103082 q = 1) : d104372 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d103082, d104372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7135 q selected
    | true =>
      simp only [d103082, d104372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7137 q selected
  have h2 (q : Pattern) (selected : d103084 q = 1) : d103084 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d103085 q = 1) : d104373 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d103085, d104373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103085, d104373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d103086 q = 1) : d104374 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d103086, d104374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103086, d104374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103087 q = 1) : d104375 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d103087, d104375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103087, d104375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d103091 q = 1) : d104379 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d103091, d104379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103091, d104379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7138 q selected
  have h8 (q : Pattern) (selected : d103092 q = 1) : d104380 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d103092, d104380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d103092, d104380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d103093 q = 1) : d104381 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d103093, d104381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d103093, d104381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d103094 q = 1) : d104382 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d103094, d104382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d103094, d104382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d103095 q = 1) : d104383 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d103095, d104383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d103095, d104383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d103124 q = 1) : d104389 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d103124, d104389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103124, d104389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7140 q selected
  have h13 (q : Pattern) (selected : d103125 q = 1) : d104390 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d103125, d104390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d103125, d104390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d103126 q = 1) : d104391 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d103126, d104391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d103126, d104391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d103127 q = 1) : d104392 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d103127, d104392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d103127, d104392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d103128 q = 1) : d104393 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d103128, d104393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d103128, d104393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d103129 q = 1) : d104394 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d103129, d104394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d103129, d104394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro7142 (p : Pattern) (selected : d103135 p = 1) : d104400 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d103130 q = 1) : d104395 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d103130, d104395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103130, d104395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7141 q selected
  have h2 (q : Pattern) (selected : d103131 q = 1) : d104396 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d103131, d104396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103131, d104396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103132 q = 1) : d104397 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d103132, d104397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103132, d104397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d103133 q = 1) : d104398 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d103133, d104398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103133, d104398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d103134 q = 1) : d104399 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d103134, d104399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103134, d104399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103135 q = 1) : d104400 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d103135, d104400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103135, d104400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7143 (p : Pattern) (selected : d103181 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d78501 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4139 q selected
    | true =>
      simp only [d78501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78502 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103178 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103179 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103180 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103181 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7144 (p : Pattern) (selected : d103196 p = 1) : d104408 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d103166 q = 1) : d103166 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d103172 q = 1) : d103172 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d103177 q = 1) : d103177 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d103182 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7143 q selected
    | true =>
      simp only [d103182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103183 q = 1) : d104404 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103183, d104404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103183, d104404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103192 q = 1) : d103192 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d103193 q = 1) : d104405 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103193, d104405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103193, d104405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d103194 q = 1) : d104406 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103194, d104406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103194, d104406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d103195 q = 1) : d104407 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103195, d104407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103195, d104407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d103196 q = 1) : d104408 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d103196, d104408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103196, d104408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro7145 (p : Pattern) (selected : d103208 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d78501 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4139 q selected
    | true =>
      simp only [d78501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78502 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103178 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103179 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103180 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103208 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7146 (p : Pattern) (selected : d103217 p = 1) : d104413 p = 1 := by
  have h0 (q : Pattern) (selected : d103166 q = 1) : d103166 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d103172 q = 1) : d103172 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d103177 q = 1) : d103177 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d103182 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7143 q selected
    | true =>
      simp only [d103182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d103183 q = 1) : d104404 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103183, d104404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103183, d104404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103192 q = 1) : d103192 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d103193 q = 1) : d104405 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103193, d104405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103193, d104405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d103194 q = 1) : d104406 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103194, d104406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103194, d104406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d103195 q = 1) : d104407 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103195, d104407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103195, d104407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d103201 q = 1) : d103201 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d103205 q = 1) : d103205 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d103207 q = 1) : d103207 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d103209 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7145 q selected
    | true =>
      simp only [d103209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d103210 q = 1) : d104409 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103210, d104409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d103210, d104409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d103213 q = 1) : d103213 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d103214 q = 1) : d104410 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103214, d104410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d103214, d104410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d103215 q = 1) : d104411 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103215, d104411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d103215, d104411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d103216 q = 1) : d104412 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103216, d104412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d103216, d104412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d103217 q = 1) : d104413 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d103217, d104413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d103217, d104413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro7147 (p : Pattern) (selected : d103226 p = 1) : d104420 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d103207 q = 1) : d103207 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d103209 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7145 q selected
    | true =>
      simp only [d103209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d103210 q = 1) : d104409 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103210, d104409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103210, d104409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d103213 q = 1) : d103213 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d103214 q = 1) : d104410 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103214, d104410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103214, d104410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103224 q = 1) : d104418 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103224, d104418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103224, d104418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d103225 q = 1) : d104419 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103225, d104419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103225, d104419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d103226 q = 1) : d104420 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d103226, d104420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103226, d104420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7148 (p : Pattern) (selected : d103244 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d78566 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4145 q selected
    | true =>
      simp only [d78566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78567 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103241 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103242 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103243 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103244 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7149 (p : Pattern) (selected : d103259 p = 1) : d104430 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d103240 q = 1) : d103240 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d103245 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7148 q selected
    | true =>
      simp only [d103245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d103246 q = 1) : d104426 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103246, d104426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103246, d104426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d103255 q = 1) : d103255 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d103256 q = 1) : d104427 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103256, d104427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103256, d104427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103257 q = 1) : d104428 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103257, d104428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103257, d104428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d103258 q = 1) : d104429 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103258, d104429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103258, d104429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d103259 q = 1) : d104430 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d103259, d104430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103259, d104430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7150 (p : Pattern) (selected : d103265 p = 1) : d104436 p = 1 := by
  have h0 (q : Pattern) (selected : d103160 q = 1) : d103160 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d103218 q = 1) : d104414 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d103218, d104414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7144 q selected
    | true =>
      simp only [d103218, d104414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7146 q selected
  have h2 (q : Pattern) (selected : d103220 q = 1) : d103220 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d103221 q = 1) : d104415 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d103221, d104415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103221, d104415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d103222 q = 1) : d104416 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d103222, d104416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103222, d104416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103223 q = 1) : d104417 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d103223, d104417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103223, d104417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d103227 q = 1) : d104421 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d103227, d104421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103227, d104421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7147 q selected
  have h8 (q : Pattern) (selected : d103228 q = 1) : d104422 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d103228, d104422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d103228, d104422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d103229 q = 1) : d104423 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d103229, d104423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d103229, d104423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d103230 q = 1) : d104424 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d103230, d104424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d103230, d104424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d103231 q = 1) : d104425 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d103231, d104425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d103231, d104425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d103260 q = 1) : d104431 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d103260, d104431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103260, d104431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7149 q selected
  have h13 (q : Pattern) (selected : d103261 q = 1) : d104432 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d103261, d104432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d103261, d104432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d103262 q = 1) : d104433 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d103262, d104433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d103262, d104433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d103263 q = 1) : d104434 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d103263, d104434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d103263, d104434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d103264 q = 1) : d104435 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d103264, d104435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d103264, d104435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d103265 q = 1) : d104436 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d103265, d104436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d103265, d104436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro7151 (p : Pattern) (selected : d103271 p = 1) : d104442 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d103266 q = 1) : d104437 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d103266, d104437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103266, d104437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7150 q selected
  have h2 (q : Pattern) (selected : d103267 q = 1) : d104438 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d103267, d104438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103267, d104438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103268 q = 1) : d104439 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d103268, d104439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103268, d104439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d103269 q = 1) : d104440 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d103269, d104440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103269, d104440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d103270 q = 1) : d104441 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d103270, d104441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103270, d104441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103271 q = 1) : d104442 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d103271, d104442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103271, d104442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7152 (p : Pattern) (selected : d103318 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d78651 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4150 q selected
    | true =>
      simp only [d78651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78652 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103315 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103316 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103317 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103318 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7153 (p : Pattern) (selected : d103333 p = 1) : d104451 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d103303 q = 1) : d103303 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d103309 q = 1) : d103309 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d103314 q = 1) : d103314 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d103319 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7152 q selected
    | true =>
      simp only [d103319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103320 q = 1) : d104447 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103320, d104447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103320, d104447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103329 q = 1) : d103329 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d103330 q = 1) : d104448 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103330, d104448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103330, d104448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d103331 q = 1) : d104449 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103331, d104449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103331, d104449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d103332 q = 1) : d104450 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103332, d104450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103332, d104450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d103333 q = 1) : d104451 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d103333, d104451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103333, d104451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro7154 (p : Pattern) (selected : d103345 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d78651 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4150 q selected
    | true =>
      simp only [d78651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78652 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103315 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103316 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103317 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103345 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7155 (p : Pattern) (selected : d103354 p = 1) : d104456 p = 1 := by
  have h0 (q : Pattern) (selected : d103303 q = 1) : d103303 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d103309 q = 1) : d103309 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d103314 q = 1) : d103314 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d103319 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7152 q selected
    | true =>
      simp only [d103319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d103320 q = 1) : d104447 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103320, d104447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103320, d104447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103329 q = 1) : d103329 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d103330 q = 1) : d104448 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103330, d104448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103330, d104448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d103331 q = 1) : d104449 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103331, d104449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103331, d104449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d103332 q = 1) : d104450 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103332, d104450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103332, d104450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d103338 q = 1) : d103338 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d103342 q = 1) : d103342 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d103344 q = 1) : d103344 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d103346 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7154 q selected
    | true =>
      simp only [d103346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d103347 q = 1) : d104452 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103347, d104452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d103347, d104452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d103350 q = 1) : d103350 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d103351 q = 1) : d104453 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103351, d104453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d103351, d104453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d103352 q = 1) : d104454 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103352, d104454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d103352, d104454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d103353 q = 1) : d104455 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103353, d104455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d103353, d104455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d103354 q = 1) : d104456 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d103354, d104456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d103354, d104456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro7156 (p : Pattern) (selected : d103363 p = 1) : d104463 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d103344 q = 1) : d103344 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d103346 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7154 q selected
    | true =>
      simp only [d103346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d103347 q = 1) : d104452 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103347, d104452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103347, d104452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d103350 q = 1) : d103350 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d103351 q = 1) : d104453 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103351, d104453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103351, d104453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103361 q = 1) : d104461 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103361, d104461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103361, d104461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d103362 q = 1) : d104462 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103362, d104462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103362, d104462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d103363 q = 1) : d104463 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d103363, d104463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103363, d104463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7157 (p : Pattern) (selected : d103381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d78716 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4156 q selected
    | true =>
      simp only [d78716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78717 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d78717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103378 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d103378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103379 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d103379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103380 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d103380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103381 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d103381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7158 (p : Pattern) (selected : d103396 p = 1) : d104473 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d103377 q = 1) : d103377 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d103382 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d103382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7157 q selected
    | true =>
      simp only [d103382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d103383 q = 1) : d104469 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d103383, d104469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103383, d104469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d103392 q = 1) : d103392 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d103393 q = 1) : d104470 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d103393, d104470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103393, d104470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103394 q = 1) : d104471 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d103394, d104471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103394, d104471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d103395 q = 1) : d104472 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103395, d104472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103395, d104472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d103396 q = 1) : d104473 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d103396, d104473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103396, d104473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7159 (p : Pattern) (selected : d103402 p = 1) : d104479 p = 1 := by
  have h0 (q : Pattern) (selected : d103297 q = 1) : d103297 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d103355 q = 1) : d104457 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d103355, d104457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7153 q selected
    | true =>
      simp only [d103355, d104457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7155 q selected
  have h2 (q : Pattern) (selected : d103357 q = 1) : d103357 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d103358 q = 1) : d104458 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d103358, d104458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103358, d104458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d103359 q = 1) : d104459 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d103359, d104459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103359, d104459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103360 q = 1) : d104460 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d103360, d104460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103360, d104460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d103364 q = 1) : d104464 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d103364, d104464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103364, d104464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7156 q selected
  have h8 (q : Pattern) (selected : d103365 q = 1) : d104465 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d103365, d104465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d103365, d104465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d103366 q = 1) : d104466 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d103366, d104466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d103366, d104466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d103367 q = 1) : d104467 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d103367, d104467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d103367, d104467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d103368 q = 1) : d104468 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d103368, d104468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d103368, d104468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d103397 q = 1) : d104474 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d103397, d104474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103397, d104474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7158 q selected
  have h13 (q : Pattern) (selected : d103398 q = 1) : d104475 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d103398, d104475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d103398, d104475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d103399 q = 1) : d104476 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d103399, d104476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d103399, d104476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d103400 q = 1) : d104477 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d103400, d104477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d103400, d104477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d103401 q = 1) : d104478 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d103401, d104478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d103401, d104478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d103402 q = 1) : d104479 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d103402, d104479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d103402, d104479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro7160 (p : Pattern) (selected : d103408 p = 1) : d104485 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d103403 q = 1) : d104480 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d103403, d104480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103403, d104480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7159 q selected
  have h2 (q : Pattern) (selected : d103404 q = 1) : d104481 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d103404, d104481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103404, d104481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d103405 q = 1) : d104482 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d103405, d104482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103405, d104482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d103406 q = 1) : d104483 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d103406, d104483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103406, d104483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d103407 q = 1) : d104484 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d103407, d104484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103407, d104484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103408 q = 1) : d104485 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d103408, d104485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103408, d104485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7161 (p : Pattern) (selected : d103414 p = 1) : d104491 p = 1 := by
  have h0 (q : Pattern) (selected : d102867 q = 1) : d104320 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d102867, d104320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7115 q selected
    | true =>
      simp only [d102867, d104320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7124 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d103001 q = 1) : d104360 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d103001, d104360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103001, d104360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7133 q selected
  have h3 (q : Pattern) (selected : d103002 q = 1) : d104361 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d103002, d104361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103002, d104361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d103136 q = 1) : d104401 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d103136, d104401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103136, d104401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7142 q selected
  have h5 (q : Pattern) (selected : d103137 q = 1) : d104402 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d103137, d104402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103137, d104402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d103138 q = 1) : d104403 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d103138, d104403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103138, d104403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d103272 q = 1) : d104443 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d103272, d104443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103272, d104443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7151 q selected
  have h8 (q : Pattern) (selected : d103273 q = 1) : d104444 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d103273, d104444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103273, d104444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d103274 q = 1) : d104445 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d103274, d104445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103274, d104445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d103275 q = 1) : d104446 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d103275, d104446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d103275, d104446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d103409 q = 1) : d104486 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d103409, d104486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103409, d104486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7160 q selected
  have h12 (q : Pattern) (selected : d103410 q = 1) : d104487 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d103410, d104487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103410, d104487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d103411 q = 1) : d104488 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d103411, d104488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103411, d104488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d103412 q = 1) : d104489 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d103412, d104489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103412, d104489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d103413 q = 1) : d104490 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d103413, d104490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d103413, d104490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d103414 q = 1) : d104491 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d103414, d104491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d103414, d104491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro7162 (p : Pattern) (selected : d103420 p = 1) : d104497 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d103415 q = 1) : d104492 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d103415, d104492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7161 q selected
    | true =>
      simp only [d103415, d104492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d103416 q = 1) : d104493 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d103416, d104493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103416, d104493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d103417 q = 1) : d104494 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d103417, d104494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103417, d104494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103418 q = 1) : d104495 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d103418, d104495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103418, d104495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103419 q = 1) : d104496 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d103419, d104496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103419, d104496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103420 q = 1) : d104497 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d103420, d104497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103420, d104497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7163 (p : Pattern) (selected : d103426 p = 1) : d104503 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d103421 q = 1) : d104498 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d103421, d104498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7162 q selected
    | true =>
      simp only [d103421, d104498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d103422 q = 1) : d104499 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d103422, d104499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103422, d104499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d103423 q = 1) : d104500 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d103423, d104500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103423, d104500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103424 q = 1) : d104501 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d103424, d104501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103424, d104501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103425 q = 1) : d104502 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d103425, d104502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103425, d104502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103426 q = 1) : d104503 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d103426, d104503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103426, d104503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7164 (p : Pattern) (selected : d103432 p = 1) : d104509 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d103427 q = 1) : d104504 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d103427, d104504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7163 q selected
    | true =>
      simp only [d103427, d104504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d103428 q = 1) : d104505 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d103428, d104505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103428, d104505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d103429 q = 1) : d104506 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d103429, d104506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103429, d104506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103430 q = 1) : d104507 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d103430, d104507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103430, d104507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103431 q = 1) : d104508 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d103431, d104508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103431, d104508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103432 q = 1) : d104509 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d103432, d104509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103432, d104509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7165 (p : Pattern) (selected : d103437 p = 1) : d104514 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d103433 q = 1) : d104510 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d103433, d104510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7164 q selected
    | true =>
      simp only [d103433, d104510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d103434 q = 1) : d104511 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d103434, d104511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103434, d104511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d103435 q = 1) : d104512 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d103435, d104512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103435, d104512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103436 q = 1) : d104513 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d103436, d104513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103436, d104513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103437 q = 1) : d104514 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d103437, d104514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103437, d104514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro7166 (p : Pattern) (selected : d103443 p = 1) : d104520 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d103438 q = 1) : d104515 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d103438, d104515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7165 q selected
    | true =>
      simp only [d103438, d104515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d103439 q = 1) : d104516 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d103439, d104516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103439, d104516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d103440 q = 1) : d104517 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d103440, d104517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103440, d104517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103441 q = 1) : d104518 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d103441, d104518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103441, d104518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103442 q = 1) : d104519 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d103442, d104519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103442, d104519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103443 q = 1) : d104520 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d103443, d104520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103443, d104520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7167 (p : Pattern) (selected : d103449 p = 1) : d104526 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d103444 q = 1) : d104521 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d103444, d104521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7166 q selected
    | true =>
      simp only [d103444, d104521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d103445 q = 1) : d104522 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d103445, d104522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103445, d104522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d103446 q = 1) : d104523 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d103446, d104523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103446, d104523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103447 q = 1) : d104524 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d103447, d104524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103447, d104524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103448 q = 1) : d104525 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d103448, d104525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103448, d104525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103449 q = 1) : d104526 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d103449, d104526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103449, d104526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7168 (p : Pattern) (selected : d103455 p = 1) : d104532 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d103450 q = 1) : d104527 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d103450, d104527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7167 q selected
    | true =>
      simp only [d103450, d104527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d103451 q = 1) : d104528 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d103451, d104528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d103451, d104528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d103452 q = 1) : d104529 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d103452, d104529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d103452, d104529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d103453 q = 1) : d104530 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d103453, d104530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d103453, d104530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d103454 q = 1) : d104531 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d103454, d104531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d103454, d104531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d103455 q = 1) : d104532 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d103455, d104532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d103455, d104532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7169 (p : Pattern) (selected : d104546 p = 0) : d105435 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d31 q = 0) : d51883 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro188 q selected
    | true =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d32 q = 0) : d51884 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d33 q = 0) : d51885 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d104546 q = 0) : d105435 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d104546, d105435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104546, d105435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7170 (p : Pattern) (selected : d104552 p = 0) : d105441 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104547 q = 0) : d105436 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104547, d105436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7169 q selected
    | true =>
      simp only [d104547, d105436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104548 q = 0) : d105437 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104548, d105437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104548, d105437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104549 q = 0) : d105438 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104549, d105438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104549, d105438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104550 q = 0) : d105439 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104550, d105439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104550, d105439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104551 q = 0) : d105440 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104551, d105440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104551, d105440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104552 q = 0) : d105441 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104552, d105441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104552, d105441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7171 (p : Pattern) (selected : d104558 p = 0) : d105447 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104553 q = 0) : d105442 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104553, d105442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7170 q selected
    | true =>
      simp only [d104553, d105442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104554 q = 0) : d105443 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104554, d105443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d104554, d105443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d104555 q = 0) : d105444 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104555, d105444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104555, d105444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104556 q = 0) : d105445 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104556, d105445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104556, d105445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104557 q = 0) : d105446 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104557, d105446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104557, d105446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104558 q = 0) : d105447 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104558, d105447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104558, d105447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7172 (p : Pattern) (selected : d104559 p = 0) : d105448 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104547 q = 0) : d105436 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104547, d105436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7169 q selected
    | true =>
      simp only [d104547, d105436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104548 q = 0) : d105437 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104548, d105437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104548, d105437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104549 q = 0) : d105438 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104549, d105438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104549, d105438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104550 q = 0) : d105439 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104550, d105439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104550, d105439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104551 q = 0) : d105440 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104551, d105440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104551, d105440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104559 q = 0) : d105448 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104559, d105448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104559, d105448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7173 (p : Pattern) (selected : d104565 p = 0) : d105454 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104553 q = 0) : d105442 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104553, d105442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7170 q selected
    | true =>
      simp only [d104553, d105442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104554 q = 0) : d105443 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104554, d105443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d104554, d105443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d104555 q = 0) : d105444 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104555, d105444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104555, d105444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104556 q = 0) : d105445 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104556, d105445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104556, d105445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104557 q = 0) : d105446 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104557, d105446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104557, d105446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104560 q = 0) : d105449 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104560, d105449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7172 q selected
    | true =>
      simp only [d104560, d105449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d104561 q = 0) : d105450 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104561, d105450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d104561, d105450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d104562 q = 0) : d105451 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104562, d105451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d104562, d105451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d104563 q = 0) : d105452 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104563, d105452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104563, d105452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d104564 q = 0) : d105453 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104564, d105453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104564, d105453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d104565 q = 0) : d105454 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104565, d105454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104565, d105454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7174 (p : Pattern) (selected : d104570 p = 0) : d105459 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104560 q = 0) : d105449 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104560, d105449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7172 q selected
    | true =>
      simp only [d104560, d105449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104561 q = 0) : d105450 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104561, d105450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d104561, d105450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d104562 q = 0) : d105451 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104562, d105451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104562, d105451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104563 q = 0) : d105452 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104563, d105452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104563, d105452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104564 q = 0) : d105453 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104564, d105453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104564, d105453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104570 q = 0) : d105459 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104570, d105459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104570, d105459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7175 (p : Pattern) (selected : d104576 p = 0) : d105465 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d72 q = 0) : d51924 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro195 q selected
    | true =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d73 q = 0) : d51925 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d74 q = 0) : d51926 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d104576 q = 0) : d105465 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d104576, d105465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104576, d105465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7176 (p : Pattern) (selected : d104582 p = 0) : d105471 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104577 q = 0) : d105466 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104577, d105466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7175 q selected
    | true =>
      simp only [d104577, d105466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104578 q = 0) : d105467 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104578, d105467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104578, d105467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104579 q = 0) : d105468 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104579, d105468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104579, d105468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104580 q = 0) : d105469 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104580, d105469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104580, d105469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104581 q = 0) : d105470 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104581, d105470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104581, d105470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104582 q = 0) : d105471 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104582, d105471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104582, d105471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7177 (p : Pattern) (selected : d104588 p = 0) : d105477 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104583 q = 0) : d105472 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104583, d105472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7176 q selected
    | true =>
      simp only [d104583, d105472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104584 q = 0) : d105473 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104584, d105473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d104584, d105473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d104585 q = 0) : d105474 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104585, d105474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104585, d105474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104586 q = 0) : d105475 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104586, d105475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104586, d105475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104587 q = 0) : d105476 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104587, d105476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104587, d105476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104588 q = 0) : d105477 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104588, d105477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104588, d105477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7178 (p : Pattern) (selected : d104594 p = 0) : d105483 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104566 q = 0) : d105455 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d104566, d105455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7171 q selected
    | true =>
      simp only [d104566, d105455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7173 q selected
  have h2 (q : Pattern) (selected : d104567 q = 0) : d105456 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d104567, d105456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d104567, d105456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d104568 q = 0) : d105457 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d104568, d105457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104568, d105457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104569 q = 0) : d105458 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d104569, d105458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104569, d105458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104571 q = 0) : d105460 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d104571, d105460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104571, d105460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7174 q selected
  have h6 (q : Pattern) (selected : d104572 q = 0) : d105461 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d104572, d105461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104572, d105461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d104573 q = 0) : d105462 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d104573, d105462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d104573, d105462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d104574 q = 0) : d105463 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d104574, d105463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d104574, d105463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d104575 q = 0) : d105464 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d104575, d105464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104575, d105464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d104589 q = 0) : d105478 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d104589, d105478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104589, d105478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7177 q selected
  have h11 (q : Pattern) (selected : d104590 q = 0) : d105479 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d104590, d105479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d104590, d105479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d104591 q = 0) : d105480 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d104591, d105480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d104591, d105480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d104592 q = 0) : d105481 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d104592, d105481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d104592, d105481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d104593 q = 0) : d105482 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d104593, d105482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d104593, d105482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d104594 q = 0) : d105483 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d104594, d105483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d104594, d105483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro7179 (p : Pattern) (selected : d104604 p = 0) : d105493 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104553 q = 0) : d105442 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104553, d105442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7170 q selected
    | true =>
      simp only [d104553, d105442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104600 q = 0) : d105489 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104600, d105489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104600, d105489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104601 q = 0) : d105490 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104601, d105490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104601, d105490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104602 q = 0) : d105491 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104602, d105491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104602, d105491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104603 q = 0) : d105492 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104603, d105492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104603, d105492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104604 q = 0) : d105493 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104604, d105493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104604, d105493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7180 (p : Pattern) (selected : d104611 p = 0) : d105500 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104553 q = 0) : d105442 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104553, d105442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7170 q selected
    | true =>
      simp only [d104553, d105442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104600 q = 0) : d105489 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104600, d105489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104600, d105489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104601 q = 0) : d105490 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104601, d105490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104601, d105490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104602 q = 0) : d105491 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104602, d105491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104602, d105491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104603 q = 0) : d105492 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104603, d105492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104603, d105492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104560 q = 0) : d105449 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104560, d105449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7172 q selected
    | true =>
      simp only [d104560, d105449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d104607 q = 0) : d105496 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104607, d105496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104607, d105496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d104608 q = 0) : d105497 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104608, d105497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d104608, d105497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d104609 q = 0) : d105498 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104609, d105498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104609, d105498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d104610 q = 0) : d105499 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104610, d105499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104610, d105499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d104611 q = 0) : d105500 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104611, d105500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104611, d105500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7181 (p : Pattern) (selected : d104616 p = 0) : d105505 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104547 q = 0) : d105436 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104547, d105436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7169 q selected
    | true =>
      simp only [d104547, d105436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104548 q = 0) : d105437 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104548, d105437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104548, d105437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104549 q = 0) : d105438 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104549, d105438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104549, d105438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104550 q = 0) : d105439 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104550, d105439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104550, d105439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104615 q = 0) : d105504 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104615, d105504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104615, d105504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104616 q = 0) : d105505 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104616, d105505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104616, d105505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7182 (p : Pattern) (selected : d104623 p = 0) : d105512 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104547 q = 0) : d105436 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104547, d105436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7169 q selected
    | true =>
      simp only [d104547, d105436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104548 q = 0) : d105437 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104548, d105437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104548, d105437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104549 q = 0) : d105438 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104549, d105438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104549, d105438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104621 q = 0) : d105510 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104621, d105510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104621, d105510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104622 q = 0) : d105511 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104622, d105511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104622, d105511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104623 q = 0) : d105512 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104623, d105512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104623, d105512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7183 (p : Pattern) (selected : d104627 p = 0) : d105516 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d145 q = 0) : d51996 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro206 q selected
    | true =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro188 q selected
  have h2 (q : Pattern) (selected : d146 q = 0) : d51997 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d51997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d146, d51997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d147 q = 0) : d51998 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d51998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d147, d51998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d104627 q = 0) : d105516 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d104627, d105516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104627, d105516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7184 (p : Pattern) (selected : d104633 p = 0) : d105522 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104628 q = 0) : d105517 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104628, d105517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7183 q selected
    | true =>
      simp only [d104628, d105517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104629 q = 0) : d105518 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104629, d105518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104629, d105518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104547 q = 0) : d105436 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104547, d105436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7169 q selected
    | true =>
      simp only [d104547, d105436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104548 q = 0) : d105437 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104548, d105437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104548, d105437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104630 q = 0) : d105519 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104630, d105519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104630, d105519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104631 q = 0) : d105520 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104631, d105520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104631, d105520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d104632 q = 0) : d105521 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104632, d105521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d104632, d105521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d104633 q = 0) : d105522 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104633, d105522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104633, d105522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7185 (p : Pattern) (selected : d104635 p = 0) : d105435 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176 q = 0) : d51883 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176, d51883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro211 q selected
    | true =>
      simp only [d176, d51883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d177 q = 0) : d51884 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177, d51884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177, d51884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d178 q = 0) : d51885 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d178, d51885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d178, d51885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d104635 q = 0) : d105435 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d104635, d105435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104635, d105435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7186 (p : Pattern) (selected : d104641 p = 0) : d105441 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104636 q = 0) : d105436 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104636, d105436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7185 q selected
    | true =>
      simp only [d104636, d105436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104637 q = 0) : d105437 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104637, d105437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104637, d105437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104638 q = 0) : d105438 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104638, d105438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104638, d105438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104639 q = 0) : d105439 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104639, d105439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104639, d105439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104640 q = 0) : d105440 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104640, d105440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104640, d105440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104641 q = 0) : d105441 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104641, d105441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104641, d105441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7187 (p : Pattern) (selected : d104647 p = 0) : d105528 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104617 q = 0) : d105506 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104617, d105506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7181 q selected
    | true =>
      simp only [d104617, d105506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104618 q = 0) : d105507 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104618, d105507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104618, d105507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104619 q = 0) : d105508 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104619, d105508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104619, d105508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104620 q = 0) : d105509 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104620, d105509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104620, d105509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104624 q = 0) : d105513 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104624, d105513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7182 q selected
    | true =>
      simp only [d104624, d105513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104625 q = 0) : d105514 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104625, d105514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104625, d105514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d104626 q = 0) : d105515 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104626, d105515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d104626, d105515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d104634 q = 0) : d105523 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104634, d105523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7184 q selected
    | true =>
      simp only [d104634, d105523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7170 q selected
  have h9 (q : Pattern) (selected : d104642 q = 0) : d105442 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104642, d105442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7186 q selected
    | true =>
      simp only [d104642, d105442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d104643 q = 0) : d105524 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104643, d105524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d104643, d105524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d104553 q = 0) : d105442 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104553, d105442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7170 q selected
    | true =>
      simp only [d104553, d105442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d104554 q = 0) : d105443 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104554, d105443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d104554, d105443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d104644 q = 0) : d105525 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104644, d105525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d104644, d105525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d104645 q = 0) : d105526 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104645, d105526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d104645, d105526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d104646 q = 0) : d105527 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104646, d105527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104646, d105527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d104647 q = 0) : d105528 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104647, d105528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104647, d105528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro7188 (p : Pattern) (selected : d104648 p = 0) : d105529 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104547 q = 0) : d105436 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104547, d105436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7169 q selected
    | true =>
      simp only [d104547, d105436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104548 q = 0) : d105437 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104548, d105437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104548, d105437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104549 q = 0) : d105438 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104549, d105438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104549, d105438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104550 q = 0) : d105439 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104550, d105439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104550, d105439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104615 q = 0) : d105504 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104615, d105504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104615, d105504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104648 q = 0) : d105529 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104648, d105529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104648, d105529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7189 (p : Pattern) (selected : d104653 p = 0) : d105534 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104547 q = 0) : d105436 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104547, d105436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7169 q selected
    | true =>
      simp only [d104547, d105436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104548 q = 0) : d105437 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104548, d105437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104548, d105437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104549 q = 0) : d105438 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104549, d105438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104549, d105438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104621 q = 0) : d105510 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104621, d105510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104621, d105510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104622 q = 0) : d105511 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104622, d105511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104622, d105511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104653 q = 0) : d105534 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104653, d105534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104653, d105534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7190 (p : Pattern) (selected : d104657 p = 0) : d105538 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104628 q = 0) : d105517 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104628, d105517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7183 q selected
    | true =>
      simp only [d104628, d105517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104629 q = 0) : d105518 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104629, d105518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104629, d105518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104547 q = 0) : d105436 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104547, d105436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7169 q selected
    | true =>
      simp only [d104547, d105436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104548 q = 0) : d105437 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104548, d105437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104548, d105437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104630 q = 0) : d105519 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104630, d105519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104630, d105519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104631 q = 0) : d105520 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104631, d105520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104631, d105520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d104632 q = 0) : d105521 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104632, d105521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d104632, d105521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d104657 q = 0) : d105538 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104657, d105538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d104657, d105538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7191 (p : Pattern) (selected : d104659 p = 0) : d105448 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104636 q = 0) : d105436 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104636, d105436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7185 q selected
    | true =>
      simp only [d104636, d105436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104637 q = 0) : d105437 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104637, d105437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104637, d105437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104638 q = 0) : d105438 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104638, d105438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104638, d105438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104639 q = 0) : d105439 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104639, d105439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104639, d105439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104640 q = 0) : d105440 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104640, d105440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104640, d105440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104659 q = 0) : d105448 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104659, d105448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104659, d105448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7192 (p : Pattern) (selected : d104665 p = 0) : d105544 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104617 q = 0) : d105506 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104617, d105506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7181 q selected
    | true =>
      simp only [d104617, d105506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104618 q = 0) : d105507 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104618, d105507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104618, d105507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104619 q = 0) : d105508 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104619, d105508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104619, d105508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104620 q = 0) : d105509 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104620, d105509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104620, d105509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104624 q = 0) : d105513 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104624, d105513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7182 q selected
    | true =>
      simp only [d104624, d105513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104625 q = 0) : d105514 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104625, d105514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104625, d105514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d104626 q = 0) : d105515 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104626, d105515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d104626, d105515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d104634 q = 0) : d105523 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104634, d105523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7184 q selected
    | true =>
      simp only [d104634, d105523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7170 q selected
  have h9 (q : Pattern) (selected : d104642 q = 0) : d105442 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104642, d105442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7186 q selected
    | true =>
      simp only [d104642, d105442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d104643 q = 0) : d105524 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104643, d105524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d104643, d105524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d104553 q = 0) : d105442 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104553, d105442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7170 q selected
    | true =>
      simp only [d104553, d105442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d104554 q = 0) : d105443 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104554, d105443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d104554, d105443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d104644 q = 0) : d105525 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104644, d105525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d104644, d105525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d104645 q = 0) : d105526 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104645, d105526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d104645, d105526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d104646 q = 0) : d105527 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104646, d105527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104646, d105527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d104649 q = 0) : d105530 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104649, d105530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7188 q selected
    | true =>
      simp only [d104649, d105530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d104650 q = 0) : d105531 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104650, d105531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104650, d105531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d104651 q = 0) : d105532 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104651, d105532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d104651, d105532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d104652 q = 0) : d105533 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104652, d105533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104652, d105533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d104654 q = 0) : d105535 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104654, d105535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7189 q selected
    | true =>
      simp only [d104654, d105535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d104655 q = 0) : d105536 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104655, d105536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104655, d105536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d104656 q = 0) : d105537 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104656, d105537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d104656, d105537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d104658 q = 0) : d105539 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104658, d105539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7190 q selected
    | true =>
      simp only [d104658, d105539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7172 q selected
  have h24 (q : Pattern) (selected : d104660 q = 0) : d105449 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104660, d105449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7191 q selected
    | true =>
      simp only [d104660, d105449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d104661 q = 0) : d105540 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104661, d105540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d104661, d105540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d104560 q = 0) : d105449 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104560, d105449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7172 q selected
    | true =>
      simp only [d104560, d105449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d104561 q = 0) : d105450 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104561, d105450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d104561, d105450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d104662 q = 0) : d105541 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104662, d105541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d104662, d105541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d104663 q = 0) : d105542 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104663, d105542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d104663, d105542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d104664 q = 0) : d105543 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104664, d105543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d104664, d105543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d104665 q = 0) : d105544 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104665, d105544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d104665, d105544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro7193 (p : Pattern) (selected : d104667 p = 0) : d105546 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104553 q = 0) : d105442 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104553, d105442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7170 q selected
    | true =>
      simp only [d104553, d105442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104600 q = 0) : d105489 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104600, d105489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104600, d105489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104601 q = 0) : d105490 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104601, d105490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104601, d105490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104602 q = 0) : d105491 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104602, d105491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104602, d105491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104603 q = 0) : d105492 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104603, d105492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104603, d105492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104667 q = 0) : d105546 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104667, d105546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104667, d105546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7194 (p : Pattern) (selected : d104674 p = 0) : d105553 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104658 q = 0) : d105539 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104658, d105539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7190 q selected
    | true =>
      simp only [d104658, d105539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7172 q selected
  have h2 (q : Pattern) (selected : d104660 q = 0) : d105449 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104660, d105449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7191 q selected
    | true =>
      simp only [d104660, d105449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d104661 q = 0) : d105540 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104661, d105540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d104661, d105540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d104560 q = 0) : d105449 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104560, d105449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7172 q selected
    | true =>
      simp only [d104560, d105449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104561 q = 0) : d105450 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104561, d105450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104561, d105450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104662 q = 0) : d105541 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104662, d105541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104662, d105541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d104672 q = 0) : d105551 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104672, d105551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104672, d105551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d104673 q = 0) : d105552 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104673, d105552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104673, d105552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d104674 q = 0) : d105553 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104674, d105553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104674, d105553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7195 (p : Pattern) (selected : d104680 p = 0) : d105559 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232 q = 0) : d52050 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro222 q selected
    | true =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro195 q selected
  have h2 (q : Pattern) (selected : d233 q = 0) : d52051 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d234 q = 0) : d52052 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d104680 q = 0) : d105559 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d104680, d105559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104680, d105559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7196 (p : Pattern) (selected : d104686 p = 0) : d105565 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104681 q = 0) : d105560 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104681, d105560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7195 q selected
    | true =>
      simp only [d104681, d105560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104682 q = 0) : d105561 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104682, d105561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104682, d105561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104577 q = 0) : d105466 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104577, d105466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7175 q selected
    | true =>
      simp only [d104577, d105466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104578 q = 0) : d105467 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104578, d105467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104578, d105467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104683 q = 0) : d105562 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104683, d105562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104683, d105562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104684 q = 0) : d105563 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104684, d105563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104684, d105563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d104685 q = 0) : d105564 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104685, d105564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d104685, d105564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d104686 q = 0) : d105565 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104686, d105565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d104686, d105565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7197 (p : Pattern) (selected : d104688 p = 0) : d105465 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d251 q = 0) : d51924 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d251, d51924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro225 q selected
    | true =>
      simp only [d251, d51924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d252 q = 0) : d51925 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d252, d51925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d252, d51925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d253 q = 0) : d51926 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d253, d51926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253, d51926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d104688 q = 0) : d105465 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d104688, d105465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104688, d105465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7198 (p : Pattern) (selected : d104694 p = 0) : d105471 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104689 q = 0) : d105466 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104689, d105466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7197 q selected
    | true =>
      simp only [d104689, d105466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104690 q = 0) : d105467 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104690, d105467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104690, d105467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104691 q = 0) : d105468 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104691, d105468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104691, d105468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104692 q = 0) : d105469 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104692, d105469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104692, d105469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104693 q = 0) : d105470 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104693, d105470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104693, d105470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104694 q = 0) : d105471 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104694, d105471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104694, d105471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7199 (p : Pattern) (selected : d104700 p = 0) : d105571 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104687 q = 0) : d105566 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104687, d105566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7196 q selected
    | true =>
      simp only [d104687, d105566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7176 q selected
  have h2 (q : Pattern) (selected : d104695 q = 0) : d105472 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104695, d105472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7198 q selected
    | true =>
      simp only [d104695, d105472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d104696 q = 0) : d105567 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104696, d105567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d104696, d105567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d104583 q = 0) : d105472 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104583, d105472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7176 q selected
    | true =>
      simp only [d104583, d105472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104584 q = 0) : d105473 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104584, d105473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104584, d105473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104697 q = 0) : d105568 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104697, d105568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104697, d105568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d104698 q = 0) : d105569 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104698, d105569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104698, d105569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d104699 q = 0) : d105570 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104699, d105570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104699, d105570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d104700 q = 0) : d105571 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104700, d105571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104700, d105571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7200 (p : Pattern) (selected : d104706 p = 0) : d105577 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104605 q = 0) : d105494 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d104605, d105494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104605, d105494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7179 q selected
  have h2 (q : Pattern) (selected : d104606 q = 0) : d105495 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d104606, d105495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d104606, d105495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d104612 q = 0) : d105501 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d104612, d105501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7179 q selected
    | true =>
      simp only [d104612, d105501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7180 q selected
  have h4 (q : Pattern) (selected : d104613 q = 0) : d105502 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d104613, d105502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104613, d105502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104614 q = 0) : d105503 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d104614, d105503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104614, d105503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104666 q = 0) : d105545 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d104666, d105545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7187 q selected
    | true =>
      simp only [d104666, d105545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7192 q selected
  have h7 (q : Pattern) (selected : d104668 q = 0) : d105547 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d104668, d105547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7193 q selected
    | true =>
      simp only [d104668, d105547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d104669 q = 0) : d105548 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d104669, d105548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d104669, d105548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d104670 q = 0) : d105549 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d104670, d105549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d104670, d105549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d104671 q = 0) : d105550 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d104671, d105550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104671, d105550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d104675 q = 0) : d105554 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d104675, d105554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104675, d105554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7194 q selected
  have h12 (q : Pattern) (selected : d104676 q = 0) : d105555 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d104676, d105555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d104676, d105555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d104677 q = 0) : d105556 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d104677, d105556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d104677, d105556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d104678 q = 0) : d105557 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d104678, d105557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d104678, d105557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d104679 q = 0) : d105558 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d104679, d105558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d104679, d105558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d104701 q = 0) : d105572 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d104701, d105572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104701, d105572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7199 q selected
  have h17 (q : Pattern) (selected : d104702 q = 0) : d105573 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d104702, d105573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d104702, d105573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d104703 q = 0) : d105574 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d104703, d105574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d104703, d105574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d104704 q = 0) : d105575 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d104704, d105575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d104704, d105575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d104705 q = 0) : d105576 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d104705, d105576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d104705, d105576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d104706 q = 0) : d105577 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d104706, d105577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d104706, d105577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro7201 (p : Pattern) (selected : d104712 p = 0) : d105583 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104595 q = 0) : d105484 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d104595, d105484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104595, d105484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7178 q selected
  have h2 (q : Pattern) (selected : d104596 q = 0) : d105485 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d104596, d105485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104596, d105485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104597 q = 0) : d105486 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d104597, d105486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104597, d105486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d104598 q = 0) : d105487 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d104598, d105487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104598, d105487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104599 q = 0) : d105488 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d104599, d105488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104599, d105488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104707 q = 0) : d105578 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d104707, d105578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104707, d105578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7200 q selected
  have h7 (q : Pattern) (selected : d104708 q = 0) : d105579 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d104708, d105579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104708, d105579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d104709 q = 0) : d105580 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d104709, d105580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104709, d105580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d104710 q = 0) : d105581 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d104710, d105581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104710, d105581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d104711 q = 0) : d105582 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d104711, d105582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104711, d105582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d104712 q = 0) : d105583 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d104712, d105583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104712, d105583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7202 (p : Pattern) (selected : d104716 p = 0) : d105587 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104628 q = 0) : d105517 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104628, d105517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7183 q selected
    | true =>
      simp only [d104628, d105517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104629 q = 0) : d105518 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104629, d105518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104629, d105518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104713 q = 0) : d105584 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104713, d105584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104713, d105584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104714 q = 0) : d105585 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104714, d105585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104714, d105585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104715 q = 0) : d105586 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104715, d105586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104715, d105586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104716 q = 0) : d105587 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104716, d105587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104716, d105587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7203 (p : Pattern) (selected : d104722 p = 0) : d105593 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104717 q = 0) : d105588 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104717, d105588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7202 q selected
    | true =>
      simp only [d104717, d105588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104718 q = 0) : d105589 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104718, d105589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104718, d105589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104719 q = 0) : d105590 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104719, d105590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104719, d105590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104720 q = 0) : d105591 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104720, d105591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104720, d105591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104721 q = 0) : d105592 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104721, d105592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104721, d105592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104722 q = 0) : d105593 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104722, d105593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104722, d105593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7204 (p : Pattern) (selected : d104725 p = 0) : d105596 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104628 q = 0) : d105517 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104628, d105517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7183 q selected
    | true =>
      simp only [d104628, d105517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104629 q = 0) : d105518 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104629, d105518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104629, d105518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104713 q = 0) : d105584 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104713, d105584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104713, d105584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104714 q = 0) : d105585 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104714, d105585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104714, d105585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104715 q = 0) : d105586 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104715, d105586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104715, d105586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104725 q = 0) : d105596 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104725, d105596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104725, d105596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7205 (p : Pattern) (selected : d104731 p = 0) : d105602 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104717 q = 0) : d105588 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104717, d105588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7202 q selected
    | true =>
      simp only [d104717, d105588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104718 q = 0) : d105589 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104718, d105589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104718, d105589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104719 q = 0) : d105590 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104719, d105590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104719, d105590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104720 q = 0) : d105591 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104720, d105591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104720, d105591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104721 q = 0) : d105592 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104721, d105592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104721, d105592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104726 q = 0) : d105597 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104726, d105597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7204 q selected
    | true =>
      simp only [d104726, d105597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d104727 q = 0) : d105598 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104727, d105598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104727, d105598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d104728 q = 0) : d105599 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104728, d105599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d104728, d105599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d104729 q = 0) : d105600 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104729, d105600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104729, d105600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d104730 q = 0) : d105601 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104730, d105601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104730, d105601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d104731 q = 0) : d105602 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104731, d105602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104731, d105602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7206 (p : Pattern) (selected : d104736 p = 0) : d105607 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104628 q = 0) : d105517 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104628, d105517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7183 q selected
    | true =>
      simp only [d104628, d105517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104629 q = 0) : d105518 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104629, d105518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104629, d105518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104713 q = 0) : d105584 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104713, d105584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104713, d105584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104714 q = 0) : d105585 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104714, d105585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104714, d105585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104735 q = 0) : d105606 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104735, d105606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104735, d105606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104736 q = 0) : d105607 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104736, d105607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104736, d105607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7207 (p : Pattern) (selected : d104743 p = 0) : d105614 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104628 q = 0) : d105517 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104628, d105517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7183 q selected
    | true =>
      simp only [d104628, d105517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104629 q = 0) : d105518 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104629, d105518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104629, d105518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104713 q = 0) : d105584 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104713, d105584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104713, d105584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104741 q = 0) : d105612 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104741, d105612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104741, d105612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104742 q = 0) : d105613 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104742, d105613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104742, d105613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104743 q = 0) : d105614 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104743, d105614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104743, d105614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7208 (p : Pattern) (selected : d104747 p = 0) : d105618 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d325 q = 0) : d52124 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d325, d52124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro236 q selected
    | true =>
      simp only [d325, d52124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro206 q selected
  have h2 (q : Pattern) (selected : d326 q = 0) : d52125 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326, d52125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d326, d52125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d327 q = 0) : d52126 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d327, d52126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d327, d52126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d104747 q = 0) : d105618 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d104747, d105618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104747, d105618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7209 (p : Pattern) (selected : d104753 p = 0) : d105624 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104748 q = 0) : d105619 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104748, d105619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7208 q selected
    | true =>
      simp only [d104748, d105619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104749 q = 0) : d105620 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104749, d105620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104749, d105620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104628 q = 0) : d105517 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104628, d105517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7183 q selected
    | true =>
      simp only [d104628, d105517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104629 q = 0) : d105518 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104629, d105518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104629, d105518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104750 q = 0) : d105621 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104750, d105621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104750, d105621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104751 q = 0) : d105622 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104751, d105622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104751, d105622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d104752 q = 0) : d105623 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104752, d105623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d104752, d105623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d104753 q = 0) : d105624 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104753, d105624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104753, d105624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7210 (p : Pattern) (selected : d104755 p = 0) : d105516 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d356 q = 0) : d51996 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d356, d51996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro241 q selected
    | true =>
      simp only [d356, d51996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro211 q selected
  have h2 (q : Pattern) (selected : d357 q = 0) : d51997 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d357, d51997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d357, d51997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d358 q = 0) : d51998 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d358, d51998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358, d51998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d104755 q = 0) : d105516 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d104755, d105516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104755, d105516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7211 (p : Pattern) (selected : d104761 p = 0) : d105587 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104756 q = 0) : d105517 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104756, d105517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7210 q selected
    | true =>
      simp only [d104756, d105517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104757 q = 0) : d105518 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104757, d105518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104757, d105518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104758 q = 0) : d105584 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104758, d105584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104758, d105584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104759 q = 0) : d105585 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104759, d105585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104759, d105585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104760 q = 0) : d105586 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104760, d105586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104760, d105586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104761 q = 0) : d105587 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104761, d105587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104761, d105587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7212 (p : Pattern) (selected : d104768 p = 0) : d105631 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104737 q = 0) : d105608 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104737, d105608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7206 q selected
    | true =>
      simp only [d104737, d105608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104738 q = 0) : d105609 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104738, d105609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104738, d105609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104739 q = 0) : d105610 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104739, d105610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104739, d105610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104740 q = 0) : d105611 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104740, d105611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104740, d105611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104744 q = 0) : d105615 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104744, d105615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7207 q selected
    | true =>
      simp only [d104744, d105615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104745 q = 0) : d105616 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104745, d105616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104745, d105616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d104746 q = 0) : d105617 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104746, d105617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d104746, d105617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d104754 q = 0) : d105625 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104754, d105625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7209 q selected
    | true =>
      simp only [d104754, d105625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7202 q selected
  have h9 (q : Pattern) (selected : d104762 q = 0) : d105588 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104762, d105588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7211 q selected
    | true =>
      simp only [d104762, d105588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d104763 q = 0) : d105626 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104763, d105626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d104763, d105626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d104717 q = 0) : d105588 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104717, d105588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7202 q selected
    | true =>
      simp only [d104717, d105588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d104764 q = 0) : d105627 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104764, d105627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d104764, d105627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d104765 q = 0) : d105628 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104765, d105628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d104765, d105628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d104766 q = 0) : d105629 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104766, d105629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d104766, d105629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d104767 q = 0) : d105630 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104767, d105630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104767, d105630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d104768 q = 0) : d105631 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104768, d105631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104768, d105631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro7213 (p : Pattern) (selected : d104769 p = 0) : d105632 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104628 q = 0) : d105517 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104628, d105517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7183 q selected
    | true =>
      simp only [d104628, d105517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104629 q = 0) : d105518 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104629, d105518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104629, d105518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104713 q = 0) : d105584 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104713, d105584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104713, d105584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104714 q = 0) : d105585 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104714, d105585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104714, d105585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104735 q = 0) : d105606 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104735, d105606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104735, d105606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104769 q = 0) : d105632 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104769, d105632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104769, d105632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7214 (p : Pattern) (selected : d104774 p = 0) : d105637 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104628 q = 0) : d105517 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104628, d105517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7183 q selected
    | true =>
      simp only [d104628, d105517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104629 q = 0) : d105518 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104629, d105518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104629, d105518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104713 q = 0) : d105584 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104713, d105584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104713, d105584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104741 q = 0) : d105612 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104741, d105612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104741, d105612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104742 q = 0) : d105613 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104742, d105613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104742, d105613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104774 q = 0) : d105637 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104774, d105637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104774, d105637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7215 (p : Pattern) (selected : d104778 p = 0) : d105641 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104748 q = 0) : d105619 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104748, d105619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7208 q selected
    | true =>
      simp only [d104748, d105619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104749 q = 0) : d105620 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104749, d105620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104749, d105620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104628 q = 0) : d105517 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104628, d105517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7183 q selected
    | true =>
      simp only [d104628, d105517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104629 q = 0) : d105518 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104629, d105518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104629, d105518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104750 q = 0) : d105621 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104750, d105621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104750, d105621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104751 q = 0) : d105622 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104751, d105622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104751, d105622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d104752 q = 0) : d105623 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104752, d105623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d104752, d105623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d104778 q = 0) : d105641 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104778, d105641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d104778, d105641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7216 (p : Pattern) (selected : d104780 p = 0) : d105596 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104756 q = 0) : d105517 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104756, d105517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7210 q selected
    | true =>
      simp only [d104756, d105517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104757 q = 0) : d105518 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104757, d105518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104757, d105518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104758 q = 0) : d105584 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104758, d105584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104758, d105584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104759 q = 0) : d105585 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104759, d105585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104759, d105585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104760 q = 0) : d105586 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104760, d105586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104760, d105586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104780 q = 0) : d105596 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104780, d105596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104780, d105596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7217 (p : Pattern) (selected : d104787 p = 0) : d105648 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104737 q = 0) : d105608 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104737, d105608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7206 q selected
    | true =>
      simp only [d104737, d105608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104738 q = 0) : d105609 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104738, d105609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104738, d105609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104739 q = 0) : d105610 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104739, d105610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104739, d105610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104740 q = 0) : d105611 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104740, d105611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104740, d105611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104744 q = 0) : d105615 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104744, d105615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7207 q selected
    | true =>
      simp only [d104744, d105615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104745 q = 0) : d105616 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104745, d105616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104745, d105616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d104746 q = 0) : d105617 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104746, d105617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d104746, d105617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d104754 q = 0) : d105625 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104754, d105625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7209 q selected
    | true =>
      simp only [d104754, d105625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7202 q selected
  have h9 (q : Pattern) (selected : d104762 q = 0) : d105588 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104762, d105588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7211 q selected
    | true =>
      simp only [d104762, d105588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d104763 q = 0) : d105626 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104763, d105626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d104763, d105626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d104717 q = 0) : d105588 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104717, d105588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7202 q selected
    | true =>
      simp only [d104717, d105588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d104764 q = 0) : d105627 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104764, d105627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d104764, d105627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d104765 q = 0) : d105628 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104765, d105628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d104765, d105628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d104766 q = 0) : d105629 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104766, d105629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d104766, d105629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d104767 q = 0) : d105630 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104767, d105630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104767, d105630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d104770 q = 0) : d105633 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104770, d105633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7213 q selected
    | true =>
      simp only [d104770, d105633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d104771 q = 0) : d105634 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104771, d105634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104771, d105634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d104772 q = 0) : d105635 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104772, d105635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d104772, d105635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d104773 q = 0) : d105636 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104773, d105636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104773, d105636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d104775 q = 0) : d105638 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104775, d105638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7214 q selected
    | true =>
      simp only [d104775, d105638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d104776 q = 0) : d105639 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104776, d105639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104776, d105639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d104777 q = 0) : d105640 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104777, d105640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d104777, d105640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d104779 q = 0) : d105642 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104779, d105642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7215 q selected
    | true =>
      simp only [d104779, d105642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7204 q selected
  have h24 (q : Pattern) (selected : d104781 q = 0) : d105597 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104781, d105597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7216 q selected
    | true =>
      simp only [d104781, d105597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d104782 q = 0) : d105643 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104782, d105643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d104782, d105643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d104726 q = 0) : d105597 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104726, d105597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7204 q selected
    | true =>
      simp only [d104726, d105597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d104783 q = 0) : d105644 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104783, d105644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d104783, d105644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d104784 q = 0) : d105645 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104784, d105645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d104784, d105645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d104785 q = 0) : d105646 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104785, d105646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d104785, d105646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d104786 q = 0) : d105647 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104786, d105647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d104786, d105647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d104787 q = 0) : d105648 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104787, d105648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d104787, d105648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro7218 (p : Pattern) (selected : d104789 p = 0) : d105650 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104717 q = 0) : d105588 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104717, d105588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7202 q selected
    | true =>
      simp only [d104717, d105588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104718 q = 0) : d105589 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104718, d105589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104718, d105589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104719 q = 0) : d105590 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104719, d105590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104719, d105590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104720 q = 0) : d105591 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104720, d105591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104720, d105591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104721 q = 0) : d105592 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104721, d105592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104721, d105592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104789 q = 0) : d105650 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104789, d105650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104789, d105650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7219 (p : Pattern) (selected : d104796 p = 0) : d105657 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104779 q = 0) : d105642 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104779, d105642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7215 q selected
    | true =>
      simp only [d104779, d105642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7204 q selected
  have h2 (q : Pattern) (selected : d104781 q = 0) : d105597 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104781, d105597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7216 q selected
    | true =>
      simp only [d104781, d105597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d104782 q = 0) : d105643 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104782, d105643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d104782, d105643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d104726 q = 0) : d105597 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104726, d105597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7204 q selected
    | true =>
      simp only [d104726, d105597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104783 q = 0) : d105644 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104783, d105644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104783, d105644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104784 q = 0) : d105645 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104784, d105645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104784, d105645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d104794 q = 0) : d105655 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104794, d105655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104794, d105655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d104795 q = 0) : d105656 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104795, d105656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104795, d105656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d104796 q = 0) : d105657 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104796, d105657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104796, d105657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7220 (p : Pattern) (selected : d104802 p = 0) : d105663 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d418 q = 0) : d52184 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, d52184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro253 q selected
    | true =>
      simp only [d418, d52184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro222 q selected
  have h2 (q : Pattern) (selected : d419 q = 0) : d52185 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, d52185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d419, d52185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d420 q = 0) : d52186 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, d52186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d420, d52186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d104802 q = 0) : d105663 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d104802, d105663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104802, d105663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7221 (p : Pattern) (selected : d104808 p = 0) : d105669 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104803 q = 0) : d105664 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104803, d105664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7220 q selected
    | true =>
      simp only [d104803, d105664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104804 q = 0) : d105665 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104804, d105665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104804, d105665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104681 q = 0) : d105560 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104681, d105560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7195 q selected
    | true =>
      simp only [d104681, d105560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104682 q = 0) : d105561 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104682, d105561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104682, d105561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104805 q = 0) : d105666 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104805, d105666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104805, d105666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104806 q = 0) : d105667 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104806, d105667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104806, d105667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d104807 q = 0) : d105668 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104807, d105668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d104807, d105668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d104808 q = 0) : d105669 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104808, d105669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d104808, d105669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7222 (p : Pattern) (selected : d104812 p = 0) : d105673 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104681 q = 0) : d105560 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104681, d105560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7195 q selected
    | true =>
      simp only [d104681, d105560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104682 q = 0) : d105561 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104682, d105561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104682, d105561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104809 q = 0) : d105670 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104809, d105670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104809, d105670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104810 q = 0) : d105671 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104810, d105671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104810, d105671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104811 q = 0) : d105672 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104811, d105672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104811, d105672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104812 q = 0) : d105673 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104812, d105673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104812, d105673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7223 (p : Pattern) (selected : d104814 p = 0) : d105559 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d437 q = 0) : d52050 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d437, d52050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro256 q selected
    | true =>
      simp only [d437, d52050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro225 q selected
  have h2 (q : Pattern) (selected : d438 q = 0) : d52051 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d438, d52051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d438, d52051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d439 q = 0) : d52052 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d439, d52052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d439, d52052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d104814 q = 0) : d105559 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d104814, d105559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104814, d105559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7224 (p : Pattern) (selected : d104820 p = 0) : d105673 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104815 q = 0) : d105560 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104815, d105560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7223 q selected
    | true =>
      simp only [d104815, d105560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104816 q = 0) : d105561 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104816, d105561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104816, d105561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104817 q = 0) : d105670 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104817, d105670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104817, d105670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104818 q = 0) : d105671 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104818, d105671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104818, d105671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104819 q = 0) : d105672 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104819, d105672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104819, d105672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104820 q = 0) : d105673 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104820, d105673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104820, d105673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7225 (p : Pattern) (selected : d104828 p = 0) : d105681 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104813 q = 0) : d105674 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104813, d105674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7221 q selected
    | true =>
      simp only [d104813, d105674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7222 q selected
  have h2 (q : Pattern) (selected : d104821 q = 0) : d105675 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104821, d105675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7224 q selected
    | true =>
      simp only [d104821, d105675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d104822 q = 0) : d105676 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104822, d105676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d104822, d105676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d104823 q = 0) : d105675 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104823, d105675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7222 q selected
    | true =>
      simp only [d104823, d105675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104824 q = 0) : d105677 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104824, d105677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104824, d105677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104825 q = 0) : d105678 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104825, d105678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104825, d105678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d104826 q = 0) : d105679 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104826, d105679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104826, d105679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d104827 q = 0) : d105680 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104827, d105680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104827, d105680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d104828 q = 0) : d105681 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104828, d105681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104828, d105681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7226 (p : Pattern) (selected : d104834 p = 0) : d105687 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104723 q = 0) : d105594 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d104723, d105594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104723, d105594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7203 q selected
  have h2 (q : Pattern) (selected : d104724 q = 0) : d105595 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d104724, d105595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d104724, d105595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d104732 q = 0) : d105603 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d104732, d105603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7203 q selected
    | true =>
      simp only [d104732, d105603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7205 q selected
  have h4 (q : Pattern) (selected : d104733 q = 0) : d105604 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d104733, d105604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104733, d105604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104734 q = 0) : d105605 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d104734, d105605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104734, d105605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104788 q = 0) : d105649 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d104788, d105649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7212 q selected
    | true =>
      simp only [d104788, d105649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7217 q selected
  have h7 (q : Pattern) (selected : d104790 q = 0) : d105651 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d104790, d105651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7218 q selected
    | true =>
      simp only [d104790, d105651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d104791 q = 0) : d105652 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d104791, d105652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d104791, d105652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d104792 q = 0) : d105653 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d104792, d105653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d104792, d105653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d104793 q = 0) : d105654 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d104793, d105654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104793, d105654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d104797 q = 0) : d105658 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d104797, d105658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104797, d105658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7219 q selected
  have h12 (q : Pattern) (selected : d104798 q = 0) : d105659 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d104798, d105659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d104798, d105659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d104799 q = 0) : d105660 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d104799, d105660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d104799, d105660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d104800 q = 0) : d105661 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d104800, d105661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d104800, d105661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d104801 q = 0) : d105662 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d104801, d105662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d104801, d105662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d104829 q = 0) : d105682 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d104829, d105682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104829, d105682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7225 q selected
  have h17 (q : Pattern) (selected : d104830 q = 0) : d105683 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d104830, d105683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d104830, d105683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d104831 q = 0) : d105684 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d104831, d105684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d104831, d105684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d104832 q = 0) : d105685 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d104832, d105685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d104832, d105685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d104833 q = 0) : d105686 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d104833, d105686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d104833, d105686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d104834 q = 0) : d105687 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d104834, d105687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d104834, d105687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro7227 (p : Pattern) (selected : d104840 p = 0) : d105693 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104835 q = 0) : d105688 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d104835, d105688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104835, d105688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7226 q selected
  have h2 (q : Pattern) (selected : d104836 q = 0) : d105689 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d104836, d105689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104836, d105689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104837 q = 0) : d105690 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d104837, d105690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104837, d105690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d104838 q = 0) : d105691 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d104838, d105691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104838, d105691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104839 q = 0) : d105692 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d104839, d105692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104839, d105692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104840 q = 0) : d105693 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d104840, d105693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104840, d105693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7228 (p : Pattern) (selected : d104842 p = 0) : d105695 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d763 q = 0) : d52440 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d52440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro319 q selected
    | true =>
      simp only [d763, d52440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro320 q selected
  have h2 (q : Pattern) (selected : d764 q = 0) : d52441 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d52441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d764, d52441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d765 q = 0) : d52442 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d52442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d765, d52442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d104842 q = 0) : d105695 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d104842, d105695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104842, d105695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7229 (p : Pattern) (selected : d104848 p = 0) : d105701 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104843 q = 0) : d105696 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104843, d105696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7228 q selected
    | true =>
      simp only [d104843, d105696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104844 q = 0) : d105697 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104844, d105697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104844, d105697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104845 q = 0) : d105698 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104845, d105698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104845, d105698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104846 q = 0) : d105699 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104846, d105699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104846, d105699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104847 q = 0) : d105700 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104847, d105700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104847, d105700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104848 q = 0) : d105701 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104848, d105701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104848, d105701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7230 (p : Pattern) (selected : d104854 p = 0) : d105707 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104849 q = 0) : d105702 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104849, d105702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7229 q selected
    | true =>
      simp only [d104849, d105702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104850 q = 0) : d105703 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104850, d105703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104850, d105703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104851 q = 0) : d105704 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104851, d105704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104851, d105704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104852 q = 0) : d105705 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104852, d105705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104852, d105705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104853 q = 0) : d105706 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104853, d105706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104853, d105706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104854 q = 0) : d105707 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104854, d105707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104854, d105707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7231 (p : Pattern) (selected : d104857 p = 0) : d105710 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104843 q = 0) : d105696 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104843, d105696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7228 q selected
    | true =>
      simp only [d104843, d105696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104844 q = 0) : d105697 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104844, d105697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104844, d105697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104845 q = 0) : d105698 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104845, d105698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104845, d105698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104846 q = 0) : d105699 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104846, d105699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104846, d105699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104847 q = 0) : d105700 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104847, d105700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104847, d105700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104857 q = 0) : d105710 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104857, d105710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104857, d105710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7232 (p : Pattern) (selected : d104863 p = 0) : d105716 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104849 q = 0) : d105702 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104849, d105702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7229 q selected
    | true =>
      simp only [d104849, d105702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104850 q = 0) : d105703 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104850, d105703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104850, d105703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104851 q = 0) : d105704 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104851, d105704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104851, d105704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104852 q = 0) : d105705 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104852, d105705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104852, d105705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104853 q = 0) : d105706 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104853, d105706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104853, d105706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104858 q = 0) : d105711 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104858, d105711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7231 q selected
    | true =>
      simp only [d104858, d105711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d104859 q = 0) : d105712 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104859, d105712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104859, d105712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d104860 q = 0) : d105713 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104860, d105713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d104860, d105713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d104861 q = 0) : d105714 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104861, d105714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104861, d105714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d104862 q = 0) : d105715 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104862, d105715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104862, d105715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d104863 q = 0) : d105716 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104863, d105716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104863, d105716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7233 (p : Pattern) (selected : d104868 p = 0) : d105721 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104843 q = 0) : d105696 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104843, d105696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7228 q selected
    | true =>
      simp only [d104843, d105696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104844 q = 0) : d105697 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104844, d105697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104844, d105697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104845 q = 0) : d105698 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104845, d105698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104845, d105698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104846 q = 0) : d105699 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104846, d105699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104846, d105699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104867 q = 0) : d105720 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104867, d105720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104867, d105720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104868 q = 0) : d105721 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104868, d105721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104868, d105721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7234 (p : Pattern) (selected : d104875 p = 0) : d105728 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104843 q = 0) : d105696 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104843, d105696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7228 q selected
    | true =>
      simp only [d104843, d105696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104844 q = 0) : d105697 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104844, d105697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104844, d105697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104845 q = 0) : d105698 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104845, d105698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104845, d105698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104873 q = 0) : d105726 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104873, d105726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104873, d105726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104874 q = 0) : d105727 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104874, d105727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104874, d105727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104875 q = 0) : d105728 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104875, d105728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104875, d105728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7235 (p : Pattern) (selected : d104879 p = 0) : d105732 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d759 q = 0) : d52436 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d759, d52436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro318 q selected
    | true =>
      simp only [d759, d52436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro319 q selected
  have h2 (q : Pattern) (selected : d760 q = 0) : d52437 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d760, d52437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d760, d52437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d761 q = 0) : d52438 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d761, d52438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d761, d52438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d104879 q = 0) : d105732 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d104879, d105732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104879, d105732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7236 (p : Pattern) (selected : d104885 p = 0) : d105738 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104880 q = 0) : d105733 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104880, d105733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7235 q selected
    | true =>
      simp only [d104880, d105733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104881 q = 0) : d105734 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104881, d105734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104881, d105734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104843 q = 0) : d105696 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104843, d105696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7228 q selected
    | true =>
      simp only [d104843, d105696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104844 q = 0) : d105697 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104844, d105697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104844, d105697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104882 q = 0) : d105735 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104882, d105735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104882, d105735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104883 q = 0) : d105736 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104883, d105736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104883, d105736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d104884 q = 0) : d105737 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104884, d105737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d104884, d105737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d104885 q = 0) : d105738 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104885, d105738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104885, d105738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7237 (p : Pattern) (selected : d104887 p = 0) : d105695 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d886 q = 0) : d52440 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d886, d52440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro344 q selected
    | true =>
      simp only [d886, d52440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro345 q selected
  have h2 (q : Pattern) (selected : d887 q = 0) : d52441 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d887, d52441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d887, d52441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d888 q = 0) : d52442 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d888, d52442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d888, d52442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d104887 q = 0) : d105695 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d104887, d105695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104887, d105695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7238 (p : Pattern) (selected : d104893 p = 0) : d105701 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104888 q = 0) : d105696 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104888, d105696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7237 q selected
    | true =>
      simp only [d104888, d105696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104889 q = 0) : d105697 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104889, d105697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104889, d105697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104890 q = 0) : d105698 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104890, d105698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104890, d105698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104891 q = 0) : d105699 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104891, d105699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104891, d105699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104892 q = 0) : d105700 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104892, d105700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104892, d105700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104893 q = 0) : d105701 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104893, d105701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104893, d105701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7239 (p : Pattern) (selected : d104900 p = 0) : d105745 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104869 q = 0) : d105722 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104869, d105722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7233 q selected
    | true =>
      simp only [d104869, d105722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104870 q = 0) : d105723 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104870, d105723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104870, d105723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104871 q = 0) : d105724 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104871, d105724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104871, d105724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104872 q = 0) : d105725 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104872, d105725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104872, d105725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104876 q = 0) : d105729 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104876, d105729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7234 q selected
    | true =>
      simp only [d104876, d105729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104877 q = 0) : d105730 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104877, d105730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104877, d105730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d104878 q = 0) : d105731 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104878, d105731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d104878, d105731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d104886 q = 0) : d105739 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104886, d105739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7236 q selected
    | true =>
      simp only [d104886, d105739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7229 q selected
  have h9 (q : Pattern) (selected : d104894 q = 0) : d105702 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104894, d105702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7238 q selected
    | true =>
      simp only [d104894, d105702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d104895 q = 0) : d105740 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104895, d105740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d104895, d105740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d104849 q = 0) : d105702 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104849, d105702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7229 q selected
    | true =>
      simp only [d104849, d105702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d104896 q = 0) : d105741 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104896, d105741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d104896, d105741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d104897 q = 0) : d105742 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104897, d105742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d104897, d105742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d104898 q = 0) : d105743 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104898, d105743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d104898, d105743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d104899 q = 0) : d105744 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104899, d105744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104899, d105744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d104900 q = 0) : d105745 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104900, d105745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104900, d105745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro7240 (p : Pattern) (selected : d104901 p = 0) : d105746 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104843 q = 0) : d105696 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104843, d105696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7228 q selected
    | true =>
      simp only [d104843, d105696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104844 q = 0) : d105697 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104844, d105697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104844, d105697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104845 q = 0) : d105698 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104845, d105698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104845, d105698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104846 q = 0) : d105699 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104846, d105699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104846, d105699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104867 q = 0) : d105720 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104867, d105720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104867, d105720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104901 q = 0) : d105746 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104901, d105746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104901, d105746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7241 (p : Pattern) (selected : d104906 p = 0) : d105751 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104843 q = 0) : d105696 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104843, d105696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7228 q selected
    | true =>
      simp only [d104843, d105696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104844 q = 0) : d105697 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104844, d105697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104844, d105697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104845 q = 0) : d105698 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104845, d105698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104845, d105698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104873 q = 0) : d105726 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104873, d105726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104873, d105726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104874 q = 0) : d105727 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104874, d105727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104874, d105727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104906 q = 0) : d105751 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104906, d105751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104906, d105751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7242 (p : Pattern) (selected : d104910 p = 0) : d105755 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104880 q = 0) : d105733 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104880, d105733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7235 q selected
    | true =>
      simp only [d104880, d105733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104881 q = 0) : d105734 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104881, d105734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104881, d105734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104843 q = 0) : d105696 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104843, d105696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7228 q selected
    | true =>
      simp only [d104843, d105696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104844 q = 0) : d105697 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104844, d105697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104844, d105697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104882 q = 0) : d105735 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104882, d105735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104882, d105735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104883 q = 0) : d105736 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104883, d105736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104883, d105736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d104884 q = 0) : d105737 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104884, d105737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d104884, d105737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d104910 q = 0) : d105755 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104910, d105755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d104910, d105755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7243 (p : Pattern) (selected : d104912 p = 0) : d105710 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104888 q = 0) : d105696 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104888, d105696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7237 q selected
    | true =>
      simp only [d104888, d105696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104889 q = 0) : d105697 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104889, d105697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104889, d105697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104890 q = 0) : d105698 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104890, d105698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104890, d105698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104891 q = 0) : d105699 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104891, d105699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104891, d105699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104892 q = 0) : d105700 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104892, d105700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104892, d105700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104912 q = 0) : d105710 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104912, d105710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104912, d105710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7244 (p : Pattern) (selected : d104919 p = 0) : d105762 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104869 q = 0) : d105722 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104869, d105722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7233 q selected
    | true =>
      simp only [d104869, d105722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104870 q = 0) : d105723 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104870, d105723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104870, d105723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104871 q = 0) : d105724 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104871, d105724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104871, d105724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104872 q = 0) : d105725 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104872, d105725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104872, d105725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104876 q = 0) : d105729 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104876, d105729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7234 q selected
    | true =>
      simp only [d104876, d105729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104877 q = 0) : d105730 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104877, d105730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104877, d105730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d104878 q = 0) : d105731 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104878, d105731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d104878, d105731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d104886 q = 0) : d105739 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104886, d105739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7236 q selected
    | true =>
      simp only [d104886, d105739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7229 q selected
  have h9 (q : Pattern) (selected : d104894 q = 0) : d105702 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104894, d105702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7238 q selected
    | true =>
      simp only [d104894, d105702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d104895 q = 0) : d105740 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104895, d105740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d104895, d105740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d104849 q = 0) : d105702 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104849, d105702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7229 q selected
    | true =>
      simp only [d104849, d105702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d104896 q = 0) : d105741 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104896, d105741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d104896, d105741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d104897 q = 0) : d105742 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104897, d105742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d104897, d105742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d104898 q = 0) : d105743 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104898, d105743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d104898, d105743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d104899 q = 0) : d105744 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104899, d105744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104899, d105744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d104902 q = 0) : d105747 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104902, d105747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7240 q selected
    | true =>
      simp only [d104902, d105747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d104903 q = 0) : d105748 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104903, d105748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104903, d105748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d104904 q = 0) : d105749 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104904, d105749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d104904, d105749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d104905 q = 0) : d105750 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104905, d105750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104905, d105750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d104907 q = 0) : d105752 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104907, d105752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7241 q selected
    | true =>
      simp only [d104907, d105752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d104908 q = 0) : d105753 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104908, d105753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104908, d105753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d104909 q = 0) : d105754 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104909, d105754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d104909, d105754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d104911 q = 0) : d105756 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104911, d105756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7242 q selected
    | true =>
      simp only [d104911, d105756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7231 q selected
  have h24 (q : Pattern) (selected : d104913 q = 0) : d105711 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104913, d105711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7243 q selected
    | true =>
      simp only [d104913, d105711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d104914 q = 0) : d105757 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104914, d105757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d104914, d105757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d104858 q = 0) : d105711 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104858, d105711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7231 q selected
    | true =>
      simp only [d104858, d105711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d104915 q = 0) : d105758 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104915, d105758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d104915, d105758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d104916 q = 0) : d105759 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104916, d105759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d104916, d105759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d104917 q = 0) : d105760 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104917, d105760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d104917, d105760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d104918 q = 0) : d105761 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104918, d105761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d104918, d105761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d104919 q = 0) : d105762 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104919, d105762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d104919, d105762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro7245 (p : Pattern) (selected : d104921 p = 0) : d105764 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104849 q = 0) : d105702 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104849, d105702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7229 q selected
    | true =>
      simp only [d104849, d105702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104850 q = 0) : d105703 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104850, d105703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104850, d105703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104851 q = 0) : d105704 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104851, d105704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104851, d105704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104852 q = 0) : d105705 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104852, d105705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104852, d105705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104853 q = 0) : d105706 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104853, d105706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104853, d105706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104921 q = 0) : d105764 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104921, d105764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104921, d105764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7246 (p : Pattern) (selected : d104928 p = 0) : d105771 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104911 q = 0) : d105756 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104911, d105756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7242 q selected
    | true =>
      simp only [d104911, d105756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7231 q selected
  have h2 (q : Pattern) (selected : d104913 q = 0) : d105711 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104913, d105711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7243 q selected
    | true =>
      simp only [d104913, d105711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d104914 q = 0) : d105757 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104914, d105757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d104914, d105757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d104858 q = 0) : d105711 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104858, d105711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7231 q selected
    | true =>
      simp only [d104858, d105711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104915 q = 0) : d105758 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104915, d105758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104915, d105758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104916 q = 0) : d105759 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104916, d105759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104916, d105759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d104926 q = 0) : d105769 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104926, d105769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104926, d105769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d104927 q = 0) : d105770 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104927, d105770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104927, d105770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d104928 q = 0) : d105771 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104928, d105771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104928, d105771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7247 (p : Pattern) (selected : d104934 p = 0) : d105777 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d982 q = 0) : d52601 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d982, d52601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro364 q selected
    | true =>
      simp only [d982, d52601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro365 q selected
  have h2 (q : Pattern) (selected : d983 q = 0) : d52602 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d983, d52602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d983, d52602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d984 q = 0) : d52603 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d984, d52603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d984, d52603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d104934 q = 0) : d105777 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d104934, d105777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104934, d105777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7248 (p : Pattern) (selected : d104937 p = 0) : d105780 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d987 q = 0) : d52606 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d52606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro365 q selected
    | true =>
      simp only [d987, d52606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro366 q selected
  have h2 (q : Pattern) (selected : d988 q = 0) : d52607 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d52607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d988, d52607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d989 q = 0) : d52608 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d52608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d989, d52608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d104937 q = 0) : d105780 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d104937, d105780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104937, d105780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7249 (p : Pattern) (selected : d104943 p = 0) : d105786 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104935 q = 0) : d105778 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104935, d105778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7247 q selected
    | true =>
      simp only [d104935, d105778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104936 q = 0) : d105779 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104936, d105779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104936, d105779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104938 q = 0) : d105781 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104938, d105781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7248 q selected
    | true =>
      simp only [d104938, d105781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104939 q = 0) : d105782 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104939, d105782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104939, d105782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104940 q = 0) : d105783 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104940, d105783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104940, d105783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104941 q = 0) : d105784 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104941, d105784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104941, d105784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d104942 q = 0) : d105785 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104942, d105785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d104942, d105785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d104943 q = 0) : d105786 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104943, d105786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d104943, d105786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
end NetHack.Soko22Hazard87
