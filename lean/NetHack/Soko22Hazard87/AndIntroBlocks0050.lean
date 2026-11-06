import NetHack.Soko22Hazard87.AndIntroBlocks0049
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro12500 (p : Pattern) (ha : d1063 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1006 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12499 q ha hb
    | true =>
      simp only [d1006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1007 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1060 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1061 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1062 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1063 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro12501 (p : Pattern) (ha : d1069 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1064 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12500 q ha hb
    | true =>
      simp only [d1064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1065 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1066 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1067 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1068 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1069 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12502 (p : Pattern) (ha : d4919 p = 1) (hb : d94755 p = 1) : d97737 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d761 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d762 q = 1) (hb : d94753 q = 1) : d762 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d763 q = 1) (hb : d94753 q = 1) : d4914 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d4914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12488 q ha hb
    | true =>
      simp only [d763, d4914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d764 q = 1) (hb : d94753 q = 1) : d4915 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d4915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d764, d4915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d765 q = 1) (hb : d94753 q = 1) : d4916 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d4916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d765, d4916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d766 q = 1) (hb : d94755 q = 1) : d97735 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d766, d94755, d97735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d766, d94755, d97735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d4916 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d4917 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4917, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d4917, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d4918 q = 1) (hb : d94755 q = 1) : d97736 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d4918, d97736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4918, d97736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d4919 q = 1) (hb : d94755 q = 1) : d97737 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d4919, d97737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4919, d97737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro12503 (p : Pattern) (ha : d6887 p = 1) (hb : d94755 p = 1) : d97743 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4920 q = 1) (hb : d94755 q = 1) : d97738 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d4920, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12502 q ha hb
    | true =>
      simp only [d4920, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4921 q = 1) (hb : d94755 q = 1) : d97739 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d4921, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4921, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12490 q ha hb
    | true =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6884 q = 1) (hb : d94755 q = 1) : d97740 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6884, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6884, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6885 q = 1) (hb : d94755 q = 1) : d97741 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6885, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6885, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6886 q = 1) (hb : d94755 q = 1) : d97742 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6886, d97742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6886, d97742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6887 q = 1) (hb : d94755 q = 1) : d97743 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6887, d97743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6887, d97743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro12504 (p : Pattern) (ha : d6908 p = 1) (hb : d94755 p = 1) : d97808 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6903 q = 1) (hb : d94755 q = 1) : d97744 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6903, d97744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12503 q ha hb
    | true =>
      simp only [d6903, d97744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12492 q ha hb
  have h2 (q : Pattern) (ha : d6904 q = 1) (hb : d94755 q = 1) : d97745 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6904, d97745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6904, d97745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6905 q = 1) (hb : d94755 q = 1) : d97746 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6905, d97746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6905, d97746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6906 q = 1) (hb : d94755 q = 1) : d97747 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6906, d97747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6906, d97747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6907 q = 1) (hb : d94755 q = 1) : d97748 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6907, d97748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6907, d97748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d939 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12492 q ha hb
    | true =>
      simp only [d939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d940 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d941 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d942 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d943 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6908 q = 1) (hb : d94755 q = 1) : d97808 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6908, d97808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6908, d97808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro12505 (p : Pattern) (ha : d804 p = 1) (hb : d94755 p = 1) : d97763 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d770 q = 1) (hb : d94755 q = 1) : d97738 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12489 q ha hb
    | true =>
      simp only [d770, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d771 q = 1) (hb : d94755 q = 1) : d97739 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12490 q ha hb
    | true =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d776 q = 1) (hb : d94755 q = 1) : d97740 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d776, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d777 q = 1) (hb : d94755 q = 1) : d97741 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d777, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d777, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d803 q = 1) (hb : d94755 q = 1) : d97762 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d803, d97762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d803, d97762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d804 q = 1) (hb : d94755 q = 1) : d97763 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d804, d97763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d804, d97763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro12506 (p : Pattern) (ha : d806 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12490 q ha hb
    | true =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d806 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12507 (p : Pattern) (ha : d813 p = 1) (hb : d94755 p = 1) : d97770 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d770 q = 1) (hb : d94755 q = 1) : d97738 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12489 q ha hb
    | true =>
      simp only [d770, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d771 q = 1) (hb : d94755 q = 1) : d97739 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12490 q ha hb
    | true =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d776 q = 1) (hb : d94755 q = 1) : d97740 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d776, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d811 q = 1) (hb : d94755 q = 1) : d97768 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d811, d97768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d811, d97768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d812 q = 1) (hb : d94755 q = 1) : d97769 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d812, d97769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d812, d97769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d813 q = 1) (hb : d94755 q = 1) : d97770 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d813, d97770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d813, d97770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro12508 (p : Pattern) (ha : d816 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12490 q ha hb
    | true =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d816 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12509 (p : Pattern) (ha : d6118 p = 1) (hb : d94755 p = 1) : d97743 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d770 q = 1) (hb : d94755 q = 1) : d97738 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12489 q ha hb
    | true =>
      simp only [d770, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d771 q = 1) (hb : d94755 q = 1) : d97739 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6115 q = 1) (hb : d94755 q = 1) : d97740 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6115, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6115, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6116 q = 1) (hb : d94755 q = 1) : d97741 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6116, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6116, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6117 q = 1) (hb : d94755 q = 1) : d97742 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6117, d97742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6117, d97742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6118 q = 1) (hb : d94755 q = 1) : d97743 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6118, d97743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6118, d97743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12510 (p : Pattern) (ha : d756 p = 1) (hb : d94753 p = 1) : d12489 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d547 q = 1) : d547 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d755 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d756 q = 1) (hb : d94753 q = 1) : d12489 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d756, d94753, d12489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d756, d94753, d12489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro12511 (p : Pattern) (ha : d845 p = 1) (hb : d94755 p = 1) : d97776 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d759 q = 1) (hb : d94753 q = 1) : d12688 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d759, d12688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12510 q ha hb
    | true =>
      simp only [d759, d12688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12488 q ha hb
  have h3 (q : Pattern) (ha : d760 q = 1) (hb : d94753 q = 1) : d12689 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d760, d12689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d760, d12689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d761 q = 1) (hb : d94753 q = 1) : d12690 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d761, d12690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d761, d12690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d843 q = 1) (hb : d94755 q = 1) : d97774 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d843, d94755, d97774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d843, d94755, d97774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d761 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d762 q = 1) (hb : d94753 q = 1) : d762 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d763 q = 1) (hb : d94753 q = 1) : d4914 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d4914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12488 q ha hb
    | true =>
      simp only [d763, d4914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d764 q = 1) (hb : d94753 q = 1) : d4915 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d4915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d764, d4915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d765 q = 1) (hb : d94753 q = 1) : d4916 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d4916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d765, d4916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d766 q = 1) (hb : d94755 q = 1) : d97735 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d766, d94755, d97735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d766, d94755, d97735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d844 q = 1) (hb : d94755 q = 1) : d97775 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d844, d97775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d844, d97775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d845 q = 1) (hb : d94755 q = 1) : d97776 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d845, d97776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d845, d97776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro12512 (p : Pattern) (ha : d6877 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d761 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6875 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6875, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6875, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d4916 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4917 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4917, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d4917, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d6876 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6877 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12513 (p : Pattern) (ha : d6883 p = 1) (hb : d94755 p = 1) : d97782 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d846 q = 1) (hb : d94755 q = 1) : d97777 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d846, d97777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12511 q ha hb
    | true =>
      simp only [d846, d97777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d847 q = 1) (hb : d94755 q = 1) : d97778 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d847, d97778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d847, d97778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6878 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12512 q ha hb
    | true =>
      simp only [d6878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6879 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6880 q = 1) (hb : d94755 q = 1) : d97779 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6880, d97779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6880, d97779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6881 q = 1) (hb : d94755 q = 1) : d97780 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6881, d97780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6881, d97780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6882 q = 1) (hb : d94755 q = 1) : d97781 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6882, d97781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6882, d97781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6883 q = 1) (hb : d94755 q = 1) : d97782 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6883, d97782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6883, d97782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro12514 (p : Pattern) (ha : d82111 p = 1) (hb : d94755 p = 1) : d97789 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d807 q = 1) (hb : d94755 q = 1) : d97764 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d807, d97764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12505 q ha hb
    | true =>
      simp only [d807, d97764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12506 q ha hb
  have h2 (q : Pattern) (ha : d808 q = 1) (hb : d94755 q = 1) : d97765 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d808, d97765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d808, d97765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d809 q = 1) (hb : d94755 q = 1) : d97766 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d809, d97766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d809, d97766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d810 q = 1) (hb : d94755 q = 1) : d97767 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d810, d97767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d810, d97767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d817 q = 1) (hb : d94755 q = 1) : d97771 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d817, d97771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12507 q ha hb
    | true =>
      simp only [d817, d97771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12508 q ha hb
  have h6 (q : Pattern) (ha : d818 q = 1) (hb : d94755 q = 1) : d97772 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d818, d97772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d818, d97772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d819 q = 1) (hb : d94755 q = 1) : d97773 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, d97773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d819, d97773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6888 q = 1) (hb : d94755 q = 1) : d97783 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6888, d97783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12513 q ha hb
    | true =>
      simp only [d6888, d97783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12503 q ha hb
  have h9 (q : Pattern) (ha : d82107 q = 1) (hb : d94755 q = 1) : d97784 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82107, d97784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d82107, d97784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6160 q = 1) (hb : d94755 q = 1) : d97744 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6160, d97744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12509 q ha hb
    | true =>
      simp only [d6160, d97744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d6161 q = 1) (hb : d94755 q = 1) : d97785 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6161, d97785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6161, d97785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d82108 q = 1) (hb : d94755 q = 1) : d97786 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82108, d97786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82108, d97786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d82109 q = 1) (hb : d94755 q = 1) : d97787 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82109, d97787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82109, d97787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d82110 q = 1) (hb : d94755 q = 1) : d97788 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82110, d97788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82110, d97788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d82111 q = 1) (hb : d94755 q = 1) : d97789 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82111, d97789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82111, d97789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro12515 (p : Pattern) (ha : d915 p = 1) (hb : d94755 p = 1) : d97790 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d770 q = 1) (hb : d94755 q = 1) : d97738 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12489 q ha hb
    | true =>
      simp only [d770, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d771 q = 1) (hb : d94755 q = 1) : d97739 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12490 q ha hb
    | true =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d776 q = 1) (hb : d94755 q = 1) : d97740 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d776, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d777 q = 1) (hb : d94755 q = 1) : d97741 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d777, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d777, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d803 q = 1) (hb : d94755 q = 1) : d97762 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d803, d97762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d803, d97762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d915 q = 1) (hb : d94755 q = 1) : d97790 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d915, d97790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d915, d97790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro12516 (p : Pattern) (ha : d916 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12490 q ha hb
    | true =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d916 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro12517 (p : Pattern) (ha : d921 p = 1) (hb : d94755 p = 1) : d97795 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d770 q = 1) (hb : d94755 q = 1) : d97738 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12489 q ha hb
    | true =>
      simp only [d770, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d771 q = 1) (hb : d94755 q = 1) : d97739 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12490 q ha hb
    | true =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d776 q = 1) (hb : d94755 q = 1) : d97740 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d776, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d811 q = 1) (hb : d94755 q = 1) : d97768 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d811, d97768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d811, d97768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d812 q = 1) (hb : d94755 q = 1) : d97769 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d812, d97769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d812, d97769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d921 q = 1) (hb : d94755 q = 1) : d97795 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d921, d97795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d921, d97795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro12518 (p : Pattern) (ha : d922 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12490 q ha hb
    | true =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d922 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro12519 (p : Pattern) (ha : d6127 p = 1) (hb : d94755 p = 1) : d97752 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d770 q = 1) (hb : d94755 q = 1) : d97738 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12489 q ha hb
    | true =>
      simp only [d770, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d771 q = 1) (hb : d94755 q = 1) : d97739 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6115 q = 1) (hb : d94755 q = 1) : d97740 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6115, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6115, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6116 q = 1) (hb : d94755 q = 1) : d97741 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6116, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6116, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6117 q = 1) (hb : d94755 q = 1) : d97742 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6117, d97742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6117, d97742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6127 q = 1) (hb : d94755 q = 1) : d97752 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6127, d97752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6127, d97752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro12520 (p : Pattern) (ha : d6894 p = 1) (hb : d94755 p = 1) : d97799 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d846 q = 1) (hb : d94755 q = 1) : d97777 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d846, d97777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12511 q ha hb
    | true =>
      simp only [d846, d97777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d847 q = 1) (hb : d94755 q = 1) : d97778 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d847, d97778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d847, d97778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6878 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12512 q ha hb
    | true =>
      simp only [d6878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6879 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6880 q = 1) (hb : d94755 q = 1) : d97779 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6880, d97779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6880, d97779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6881 q = 1) (hb : d94755 q = 1) : d97780 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6881, d97780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6881, d97780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6882 q = 1) (hb : d94755 q = 1) : d97781 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6882, d97781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6882, d97781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6894 q = 1) (hb : d94755 q = 1) : d97799 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6894, d97799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6894, d97799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro12521 (p : Pattern) (ha : d6895 p = 1) (hb : d94755 p = 1) : d97752 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4920 q = 1) (hb : d94755 q = 1) : d97738 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d4920, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12502 q ha hb
    | true =>
      simp only [d4920, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4921 q = 1) (hb : d94755 q = 1) : d97739 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d4921, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4921, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12490 q ha hb
    | true =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6884 q = 1) (hb : d94755 q = 1) : d97740 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6884, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6884, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6885 q = 1) (hb : d94755 q = 1) : d97741 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6885, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6885, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6886 q = 1) (hb : d94755 q = 1) : d97742 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6886, d97742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6886, d97742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6895 q = 1) (hb : d94755 q = 1) : d97752 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6895, d97752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6895, d97752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro12522 (p : Pattern) (ha : d82116 p = 1) (hb : d94755 p = 1) : d97806 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d807 q = 1) (hb : d94755 q = 1) : d97764 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d807, d97764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12505 q ha hb
    | true =>
      simp only [d807, d97764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12506 q ha hb
  have h2 (q : Pattern) (ha : d808 q = 1) (hb : d94755 q = 1) : d97765 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d808, d97765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d808, d97765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d809 q = 1) (hb : d94755 q = 1) : d97766 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d809, d97766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d809, d97766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d810 q = 1) (hb : d94755 q = 1) : d97767 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d810, d97767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d810, d97767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d817 q = 1) (hb : d94755 q = 1) : d97771 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d817, d97771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12507 q ha hb
    | true =>
      simp only [d817, d97771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12508 q ha hb
  have h6 (q : Pattern) (ha : d818 q = 1) (hb : d94755 q = 1) : d97772 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d818, d97772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d818, d97772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d819 q = 1) (hb : d94755 q = 1) : d97773 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, d97773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d819, d97773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6888 q = 1) (hb : d94755 q = 1) : d97783 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6888, d97783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12513 q ha hb
    | true =>
      simp only [d6888, d97783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12503 q ha hb
  have h9 (q : Pattern) (ha : d82107 q = 1) (hb : d94755 q = 1) : d97784 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82107, d97784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d82107, d97784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6160 q = 1) (hb : d94755 q = 1) : d97744 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6160, d97744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12509 q ha hb
    | true =>
      simp only [d6160, d97744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d6161 q = 1) (hb : d94755 q = 1) : d97785 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6161, d97785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6161, d97785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d82108 q = 1) (hb : d94755 q = 1) : d97786 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82108, d97786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82108, d97786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d82109 q = 1) (hb : d94755 q = 1) : d97787 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82109, d97787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82109, d97787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d82110 q = 1) (hb : d94755 q = 1) : d97788 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82110, d97788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82110, d97788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d917 q = 1) (hb : d94755 q = 1) : d97791 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d917, d97791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12515 q ha hb
    | true =>
      simp only [d917, d97791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12516 q ha hb
  have h16 (q : Pattern) (ha : d918 q = 1) (hb : d94755 q = 1) : d97792 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d918, d97792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d918, d97792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d919 q = 1) (hb : d94755 q = 1) : d97793 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d919, d97793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d919, d97793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d920 q = 1) (hb : d94755 q = 1) : d97794 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d920, d97794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d920, d97794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d923 q = 1) (hb : d94755 q = 1) : d97796 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d923, d97796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12517 q ha hb
    | true =>
      simp only [d923, d97796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12518 q ha hb
  have h20 (q : Pattern) (ha : d924 q = 1) (hb : d94755 q = 1) : d97797 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d924, d97797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d924, d97797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d925 q = 1) (hb : d94755 q = 1) : d97798 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d925, d97798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d925, d97798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d6896 q = 1) (hb : d94755 q = 1) : d97800 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6896, d97800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12520 q ha hb
    | true =>
      simp only [d6896, d97800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12521 q ha hb
  have h23 (q : Pattern) (ha : d82112 q = 1) (hb : d94755 q = 1) : d97801 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82112, d97801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d82112, d97801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d6181 q = 1) (hb : d94755 q = 1) : d97753 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6181, d97753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12519 q ha hb
    | true =>
      simp only [d6181, d97753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d6182 q = 1) (hb : d94755 q = 1) : d97802 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6182, d97802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d6182, d97802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d82113 q = 1) (hb : d94755 q = 1) : d97803 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82113, d97803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d82113, d97803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d82114 q = 1) (hb : d94755 q = 1) : d97804 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82114, d97804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d82114, d97804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d82115 q = 1) (hb : d94755 q = 1) : d97805 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82115, d97805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d82115, d97805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d82116 q = 1) (hb : d94755 q = 1) : d97806 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82116, d97806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d82116, d97806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro12523 (p : Pattern) (ha : d82123 p = 1) (hb : d94755 p = 1) : d97815 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6896 q = 1) (hb : d94755 q = 1) : d97800 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6896, d97800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12520 q ha hb
    | true =>
      simp only [d6896, d97800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12521 q ha hb
  have h2 (q : Pattern) (ha : d82112 q = 1) (hb : d94755 q = 1) : d97801 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82112, d97801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82112, d97801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6181 q = 1) (hb : d94755 q = 1) : d97753 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6181, d97753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12519 q ha hb
    | true =>
      simp only [d6181, d97753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6182 q = 1) (hb : d94755 q = 1) : d97802 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6182, d97802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6182, d97802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82113 q = 1) (hb : d94755 q = 1) : d97803 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82113, d97803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82113, d97803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82121 q = 1) (hb : d94755 q = 1) : d97813 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82121, d97813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82121, d97813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82122 q = 1) (hb : d94755 q = 1) : d97814 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82122, d97814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82122, d97814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82123 q = 1) (hb : d94755 q = 1) : d97815 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82123, d97815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82123, d97815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro12524 (p : Pattern) (ha : d981 p = 1) (hb : d94753 p = 1) : d6210 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d975 q = 1) : d975 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d980 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d981 q = 1) (hb : d94753 q = 1) : d6210 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d981, d94753, d6210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d981, d94753, d6210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro12525 (p : Pattern) (ha : d997 p = 1) (hb : d94755 p = 1) : d97832 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d984 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d986 q = 1) (hb : d94753 q = 1) : d986 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d987 q = 1) (hb : d94753 q = 1) : d6211 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d6211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12524 q ha hb
    | true =>
      simp only [d987, d6211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d988 q = 1) (hb : d94753 q = 1) : d6212 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d6212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d988, d6212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d989 q = 1) (hb : d94753 q = 1) : d6213 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d6213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d989, d6213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d990 q = 1) (hb : d94755 q = 1) : d97822 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d990, d94755, d97822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d990, d94755, d97822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d989 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d995 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d995, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d996 q = 1) (hb : d94755 q = 1) : d97831 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d996, d97831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d996, d97831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d997 q = 1) (hb : d94755 q = 1) : d97832 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d997, d97832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d997, d97832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro12526 (p : Pattern) (ha : d6233 p = 1) (hb : d94755 p = 1) : d97838 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d998 q = 1) (hb : d94755 q = 1) : d97833 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d998, d97833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12525 q ha hb
    | true =>
      simp only [d998, d97833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d999 q = 1) (hb : d94755 q = 1) : d97834 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d999, d97834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d999, d97834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6230 q = 1) (hb : d94755 q = 1) : d97835 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6230, d97835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6230, d97835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6231 q = 1) (hb : d94755 q = 1) : d97836 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6231, d97836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6231, d97836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6232 q = 1) (hb : d94755 q = 1) : d97837 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6232, d97837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6232, d97837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6233 q = 1) (hb : d94755 q = 1) : d97838 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6233, d97838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6233, d97838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro12527 (p : Pattern) (ha : d976 p = 1) (hb : d94753 p = 1) : d12595 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d663 q = 1) : d663 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d975 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d976 q = 1) (hb : d94753 q = 1) : d12595 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d976, d94753, d12595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d976, d94753, d12595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro12528 (p : Pattern) (ha : d992 p = 1) (hb : d94755 p = 1) : d97824 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d979 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d982 q = 1) (hb : d94753 q = 1) : d12868 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d982, d12868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12527 q ha hb
    | true =>
      simp only [d982, d12868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12524 q ha hb
  have h3 (q : Pattern) (ha : d983 q = 1) (hb : d94753 q = 1) : d12869 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d983, d12869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d983, d12869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d984 q = 1) (hb : d94753 q = 1) : d12870 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d984, d12870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d984, d12870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d985 q = 1) (hb : d94755 q = 1) : d97821 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d985, d94755, d97821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d985, d94755, d97821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d984 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d986 q = 1) (hb : d94753 q = 1) : d986 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d987 q = 1) (hb : d94753 q = 1) : d6211 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d6211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12524 q ha hb
    | true =>
      simp only [d987, d6211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d988 q = 1) (hb : d94753 q = 1) : d6212 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d6212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d988, d6212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d989 q = 1) (hb : d94753 q = 1) : d6213 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d6213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d989, d6213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d990 q = 1) (hb : d94755 q = 1) : d97822 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d990, d94755, d97822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d990, d94755, d97822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d991 q = 1) (hb : d94755 q = 1) : d97823 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d991, d97823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d991, d97823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d992 q = 1) (hb : d94755 q = 1) : d97824 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d992, d97824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d992, d97824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro12529 (p : Pattern) (ha : d6923 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d984 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6921 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6921, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6921, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6213 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6214 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6214, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d6214, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d6922 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6923 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12530 (p : Pattern) (ha : d6929 p = 1) (hb : d94755 p = 1) : d97830 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d993 q = 1) (hb : d94755 q = 1) : d97825 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d993, d97825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12528 q ha hb
    | true =>
      simp only [d993, d97825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d994 q = 1) (hb : d94755 q = 1) : d97826 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d994, d97826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d994, d97826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6924 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12529 q ha hb
    | true =>
      simp only [d6924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6925 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6926 q = 1) (hb : d94755 q = 1) : d97827 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6926, d97827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6926, d97827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6927 q = 1) (hb : d94755 q = 1) : d97828 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6927, d97828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6927, d97828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6928 q = 1) (hb : d94755 q = 1) : d97829 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6928, d97829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6928, d97829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6929 q = 1) (hb : d94755 q = 1) : d97830 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6929, d97830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6929, d97830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro12531 (p : Pattern) (ha : d6216 p = 1) (hb : d94755 p = 1) : d97832 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d984 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d986 q = 1) (hb : d94753 q = 1) : d986 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d987 q = 1) (hb : d94753 q = 1) : d6211 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d6211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12524 q ha hb
    | true =>
      simp only [d987, d6211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d988 q = 1) (hb : d94753 q = 1) : d6212 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d6212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d988, d6212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d989 q = 1) (hb : d94753 q = 1) : d6213 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d6213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d989, d6213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d990 q = 1) (hb : d94755 q = 1) : d97822 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d990, d94755, d97822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d990, d94755, d97822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d6213 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6214 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6214, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d6214, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d6215 q = 1) (hb : d94755 q = 1) : d97831 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6215, d97831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6215, d97831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d6216 q = 1) (hb : d94755 q = 1) : d97832 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6216, d97832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6216, d97832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro12532 (p : Pattern) (ha : d6933 p = 1) (hb : d94755 p = 1) : d97838 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6217 q = 1) (hb : d94755 q = 1) : d97833 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6217, d97833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12531 q ha hb
    | true =>
      simp only [d6217, d97833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6218 q = 1) (hb : d94755 q = 1) : d97834 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6218, d97834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6218, d97834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1006 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12499 q ha hb
    | true =>
      simp only [d1006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1007 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6930 q = 1) (hb : d94755 q = 1) : d97835 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6930, d97835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6930, d97835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6931 q = 1) (hb : d94755 q = 1) : d97836 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6931, d97836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6931, d97836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6932 q = 1) (hb : d94755 q = 1) : d97837 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6932, d97837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6932, d97837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6933 q = 1) (hb : d94755 q = 1) : d97838 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6933, d97838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6933, d97838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro12533 (p : Pattern) (ha : d82133 p = 1) (hb : d94755 p = 1) : d97846 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6934 q = 1) (hb : d94755 q = 1) : d97839 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6934, d97839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12530 q ha hb
    | true =>
      simp only [d6934, d97839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12532 q ha hb
  have h2 (q : Pattern) (ha : d82129 q = 1) (hb : d94755 q = 1) : d97840 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82129, d97840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82129, d97840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6234 q = 1) (hb : d94755 q = 1) : d97841 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6234, d97841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12526 q ha hb
    | true =>
      simp only [d6234, d97841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6235 q = 1) (hb : d94755 q = 1) : d97842 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6235, d97842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6235, d97842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82130 q = 1) (hb : d94755 q = 1) : d97843 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82130, d97843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82130, d97843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82131 q = 1) (hb : d94755 q = 1) : d97844 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82131, d97844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82131, d97844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82132 q = 1) (hb : d94755 q = 1) : d97845 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82132, d97845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82132, d97845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82133 q = 1) (hb : d94755 q = 1) : d97846 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82133, d97846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82133, d97846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro12534 (p : Pattern) (ha : d82139 p = 1) (hb : d94755 p = 1) : d97852 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d790 q = 1) (hb : d94755 q = 1) : d97750 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d790, d97750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d790, d97750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12493 q ha hb
  have h2 (q : Pattern) (ha : d791 q = 1) (hb : d94755 q = 1) : d97751 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d791, d97751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d791, d97751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d800 q = 1) (hb : d94755 q = 1) : d97759 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d97759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12493 q ha hb
    | true =>
      simp only [d800, d97759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12496 q ha hb
  have h4 (q : Pattern) (ha : d801 q = 1) (hb : d94755 q = 1) : d97760 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d97760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d801, d97760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d802 q = 1) (hb : d94755 q = 1) : d97761 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d802, d97761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d802, d97761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82117 q = 1) (hb : d94755 q = 1) : d97807 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82117, d97807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12514 q ha hb
    | true =>
      simp only [d82117, d97807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12522 q ha hb
  have h7 (q : Pattern) (ha : d6909 q = 1) (hb : d94755 q = 1) : d97809 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6909, d97809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12504 q ha hb
    | true =>
      simp only [d6909, d97809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12497 q ha hb
  have h8 (q : Pattern) (ha : d82118 q = 1) (hb : d94755 q = 1) : d97810 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82118, d97810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82118, d97810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d82119 q = 1) (hb : d94755 q = 1) : d97811 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82119, d97811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d82119, d97811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d82120 q = 1) (hb : d94755 q = 1) : d97812 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82120, d97812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82120, d97812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d82124 q = 1) (hb : d94755 q = 1) : d97816 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82124, d97816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82124, d97816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12523 q ha hb
  have h12 (q : Pattern) (ha : d960 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12498 q ha hb
  have h13 (q : Pattern) (ha : d82125 q = 1) (hb : d94755 q = 1) : d97817 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82125, d97817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82125, d97817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d82126 q = 1) (hb : d94755 q = 1) : d97818 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82126, d97818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82126, d97818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d82127 q = 1) (hb : d94755 q = 1) : d97819 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82127, d97819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d82127, d97819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d82128 q = 1) (hb : d94755 q = 1) : d97820 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82128, d97820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82128, d97820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d82134 q = 1) (hb : d94755 q = 1) : d97847 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82134, d97847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82134, d97847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12533 q ha hb
  have h18 (q : Pattern) (ha : d1070 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12501 q ha hb
  have h19 (q : Pattern) (ha : d82135 q = 1) (hb : d94755 q = 1) : d97848 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82135, d97848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d82135, d97848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d82136 q = 1) (hb : d94755 q = 1) : d97849 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82136, d97849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d82136, d97849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d82137 q = 1) (hb : d94755 q = 1) : d97850 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82137, d97850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d82137, d97850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d82138 q = 1) (hb : d94755 q = 1) : d97851 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82138, d97851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d82138, d97851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d82139 q = 1) (hb : d94755 q = 1) : d97852 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82139, d97852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d82139, d97852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro12535 (p : Pattern) (ha : d82145 p = 1) (hb : d94755 p = 1) : d97858 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82140 q = 1) (hb : d94755 q = 1) : d97853 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82140, d97853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82140, d97853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12534 q ha hb
  have h2 (q : Pattern) (ha : d82141 q = 1) (hb : d94755 q = 1) : d97854 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82141, d97854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82141, d97854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82142 q = 1) (hb : d94755 q = 1) : d97855 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82142, d97855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82142, d97855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82143 q = 1) (hb : d94755 q = 1) : d97856 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82143, d97856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82143, d97856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82144 q = 1) (hb : d94755 q = 1) : d97857 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82144, d97857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82144, d97857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82145 q = 1) (hb : d94755 q = 1) : d97858 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82145, d97858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82145, d97858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12536 (p : Pattern) (ha : d1128 p = 1) (hb : d94753 p = 1) : d5009 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1125 q = 1) : d1125 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1127 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1128 q = 1) (hb : d94753 q = 1) : d5009 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1128, d94753, d5009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1128, d94753, d5009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro12537 (p : Pattern) (ha : d1141 p = 1) (hb : d94753 p = 1) : d12961 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1127 q = 1) : d1127 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1140 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1141 q = 1) (hb : d94753 q = 1) : d12961 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1141, d94753, d12961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1141, d94753, d12961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro12538 (p : Pattern) (ha : d1148 p = 1) (hb : d94755 p = 1) : d97863 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1131 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1142 q = 1) (hb : d94753 q = 1) : d12962 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1142, d12962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12536 q ha hb
    | true =>
      simp only [d1142, d12962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12537 q ha hb
  have h3 (q : Pattern) (ha : d1143 q = 1) (hb : d94753 q = 1) : d12963 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1143, d12963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1143, d12963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1144 q = 1) (hb : d94753 q = 1) : d12964 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1144, d12964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1144, d12964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1145 q = 1) (hb : d94755 q = 1) : d97861 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1145, d94755, d97861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1145, d94755, d97861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1144 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1146 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1146, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1146, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1147 q = 1) (hb : d94755 q = 1) : d97862 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1147, d97862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1147, d97862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1148 q = 1) (hb : d94755 q = 1) : d97863 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1148, d97863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1148, d97863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro12539 (p : Pattern) (ha : d1152 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1144 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1146 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1146, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1146, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1151 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1152 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro12540 (p : Pattern) (ha : d1158 p = 1) (hb : d94755 p = 1) : d97869 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1149 q = 1) (hb : d94755 q = 1) : d97864 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12538 q ha hb
    | true =>
      simp only [d1149, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1150 q = 1) (hb : d94755 q = 1) : d97865 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12539 q ha hb
    | true =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1155 q = 1) (hb : d94755 q = 1) : d97866 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1155, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1156 q = 1) (hb : d94755 q = 1) : d97867 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1156, d97867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1156, d97867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1157 q = 1) (hb : d94755 q = 1) : d97868 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1157, d97868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1157, d97868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1158 q = 1) (hb : d94755 q = 1) : d97869 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1158, d97869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1158, d97869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro12541 (p : Pattern) (ha : d1162 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12539 q ha hb
    | true =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1161 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1162 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12542 (p : Pattern) (ha : d1168 p = 1) (hb : d94755 p = 1) : d97875 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1163 q = 1) (hb : d94755 q = 1) : d97870 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1163, d97870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12540 q ha hb
    | true =>
      simp only [d1163, d97870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12541 q ha hb
  have h2 (q : Pattern) (ha : d1164 q = 1) (hb : d94755 q = 1) : d97871 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d97871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1164, d97871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1165 q = 1) (hb : d94755 q = 1) : d97872 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d97872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1165, d97872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1166 q = 1) (hb : d94755 q = 1) : d97873 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, d97873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1166, d97873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1167 q = 1) (hb : d94755 q = 1) : d97874 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, d97874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, d97874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1168 q = 1) (hb : d94755 q = 1) : d97875 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1168, d97875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1168, d97875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12543 (p : Pattern) (ha : d1171 p = 1) (hb : d94755 p = 1) : d97878 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1149 q = 1) (hb : d94755 q = 1) : d97864 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12538 q ha hb
    | true =>
      simp only [d1149, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1150 q = 1) (hb : d94755 q = 1) : d97865 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12539 q ha hb
    | true =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1155 q = 1) (hb : d94755 q = 1) : d97866 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1155, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1156 q = 1) (hb : d94755 q = 1) : d97867 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1156, d97867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1156, d97867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1157 q = 1) (hb : d94755 q = 1) : d97868 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1157, d97868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1157, d97868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1171 q = 1) (hb : d94755 q = 1) : d97878 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1171, d97878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1171, d97878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro12544 (p : Pattern) (ha : d1172 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12539 q ha hb
    | true =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1161 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1172 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro12545 (p : Pattern) (ha : d1178 p = 1) (hb : d94755 p = 1) : d97884 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1163 q = 1) (hb : d94755 q = 1) : d97870 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1163, d97870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12540 q ha hb
    | true =>
      simp only [d1163, d97870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12541 q ha hb
  have h2 (q : Pattern) (ha : d1164 q = 1) (hb : d94755 q = 1) : d97871 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d97871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1164, d97871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1165 q = 1) (hb : d94755 q = 1) : d97872 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d97872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1165, d97872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1166 q = 1) (hb : d94755 q = 1) : d97873 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, d97873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1166, d97873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1167 q = 1) (hb : d94755 q = 1) : d97874 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, d97874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, d97874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1173 q = 1) (hb : d94755 q = 1) : d97879 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1173, d97879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12543 q ha hb
    | true =>
      simp only [d1173, d97879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12544 q ha hb
  have h7 (q : Pattern) (ha : d1174 q = 1) (hb : d94755 q = 1) : d97880 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1174, d97880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1174, d97880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1175 q = 1) (hb : d94755 q = 1) : d97881 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1175, d97881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1175, d97881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1176 q = 1) (hb : d94755 q = 1) : d97882 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1176, d97882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1176, d97882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1177 q = 1) (hb : d94755 q = 1) : d97883 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1177, d97883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1177, d97883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1178 q = 1) (hb : d94755 q = 1) : d97884 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1178, d97884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1178, d97884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro12546 (p : Pattern) (ha : d1361 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1350 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12541 q ha hb
    | true =>
      simp only [d1350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1351 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1352 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1353 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1354 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1356 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12544 q ha hb
    | true =>
      simp only [d1356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1357 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1358 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1359 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1360 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1361 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro12547 (p : Pattern) (ha : d1370 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1356 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12544 q ha hb
    | true =>
      simp only [d1356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1357 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1358 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1359 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1360 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1370 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12548 (p : Pattern) (ha : d1430 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1414 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1420 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1420, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1420, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1429 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1430 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro12549 (p : Pattern) (ha : d1497 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1431 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12548 q ha hb
    | true =>
      simp only [d1431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1432 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1494 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1495 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1496 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1497 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro12550 (p : Pattern) (ha : d1503 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1498 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12549 q ha hb
    | true =>
      simp only [d1498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1499 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1500 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1501 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1502 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1503 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12551 (p : Pattern) (ha : d5029 p = 1) (hb : d94755 p = 1) : d97863 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1131 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1142 q = 1) (hb : d94753 q = 1) : d12962 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1142, d12962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12536 q ha hb
    | true =>
      simp only [d1142, d12962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12537 q ha hb
  have h3 (q : Pattern) (ha : d1143 q = 1) (hb : d94753 q = 1) : d12963 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1143, d12963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1143, d12963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1144 q = 1) (hb : d94753 q = 1) : d12964 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1144, d12964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1144, d12964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1145 q = 1) (hb : d94755 q = 1) : d97861 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1145, d94755, d97861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1145, d94755, d97861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5026 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5027 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5027, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d5027, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d5028 q = 1) (hb : d94755 q = 1) : d97862 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d5028, d97862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5028, d97862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d5029 q = 1) (hb : d94755 q = 1) : d97863 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d5029, d97863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5029, d97863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro12552 (p : Pattern) (ha : d6966 p = 1) (hb : d94755 p = 1) : d97869 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5030 q = 1) (hb : d94755 q = 1) : d97864 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5030, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12551 q ha hb
    | true =>
      simp only [d5030, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5031 q = 1) (hb : d94755 q = 1) : d97865 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5031, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5031, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12539 q ha hb
    | true =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6963 q = 1) (hb : d94755 q = 1) : d97866 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6963, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6963, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6964 q = 1) (hb : d94755 q = 1) : d97867 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6964, d97867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6964, d97867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6965 q = 1) (hb : d94755 q = 1) : d97868 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6965, d97868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6965, d97868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6966 q = 1) (hb : d94755 q = 1) : d97869 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6966, d97869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6966, d97869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro12553 (p : Pattern) (ha : d6987 p = 1) (hb : d94755 p = 1) : d97934 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6982 q = 1) (hb : d94755 q = 1) : d97870 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6982, d97870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12552 q ha hb
    | true =>
      simp only [d6982, d97870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12541 q ha hb
  have h2 (q : Pattern) (ha : d6983 q = 1) (hb : d94755 q = 1) : d97871 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6983, d97871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6983, d97871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6984 q = 1) (hb : d94755 q = 1) : d97872 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6984, d97872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6984, d97872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6985 q = 1) (hb : d94755 q = 1) : d97873 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6985, d97873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6985, d97873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6986 q = 1) (hb : d94755 q = 1) : d97874 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6986, d97874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6986, d97874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1350 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12541 q ha hb
    | true =>
      simp only [d1350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1351 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1352 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1353 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1354 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6987 q = 1) (hb : d94755 q = 1) : d97934 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6987, d97934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6987, d97934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro12554 (p : Pattern) (ha : d1183 p = 1) (hb : d94755 p = 1) : d97889 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1149 q = 1) (hb : d94755 q = 1) : d97864 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12538 q ha hb
    | true =>
      simp only [d1149, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1150 q = 1) (hb : d94755 q = 1) : d97865 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12539 q ha hb
    | true =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1155 q = 1) (hb : d94755 q = 1) : d97866 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1155, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1156 q = 1) (hb : d94755 q = 1) : d97867 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1156, d97867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1156, d97867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1182 q = 1) (hb : d94755 q = 1) : d97888 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1182, d97888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1182, d97888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1183 q = 1) (hb : d94755 q = 1) : d97889 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1183, d97889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1183, d97889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro12555 (p : Pattern) (ha : d1185 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12539 q ha hb
    | true =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1184 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1185 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12556 (p : Pattern) (ha : d1192 p = 1) (hb : d94755 p = 1) : d97896 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1149 q = 1) (hb : d94755 q = 1) : d97864 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12538 q ha hb
    | true =>
      simp only [d1149, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1150 q = 1) (hb : d94755 q = 1) : d97865 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12539 q ha hb
    | true =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1155 q = 1) (hb : d94755 q = 1) : d97866 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1155, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1190 q = 1) (hb : d94755 q = 1) : d97894 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1190, d97894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1190, d97894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1191 q = 1) (hb : d94755 q = 1) : d97895 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1191, d97895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1191, d97895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1192 q = 1) (hb : d94755 q = 1) : d97896 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1192, d97896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1192, d97896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro12557 (p : Pattern) (ha : d1195 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12539 q ha hb
    | true =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1193 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1194 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1195 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12558 (p : Pattern) (ha : d6257 p = 1) (hb : d94755 p = 1) : d97869 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1149 q = 1) (hb : d94755 q = 1) : d97864 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12538 q ha hb
    | true =>
      simp only [d1149, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1150 q = 1) (hb : d94755 q = 1) : d97865 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6254 q = 1) (hb : d94755 q = 1) : d97866 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6254, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6254, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6255 q = 1) (hb : d94755 q = 1) : d97867 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6255, d97867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6255, d97867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6256 q = 1) (hb : d94755 q = 1) : d97868 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6256, d97868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6256, d97868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6257 q = 1) (hb : d94755 q = 1) : d97869 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6257, d97869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6257, d97869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12559 (p : Pattern) (ha : d1126 p = 1) (hb : d94753 p = 1) : d12956 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1114 q = 1) : d1114 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1125 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1126 q = 1) (hb : d94753 q = 1) : d12956 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1126, d94753, d12956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1126, d94753, d12956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro12560 (p : Pattern) (ha : d1221 p = 1) (hb : d94755 p = 1) : d97902 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1218 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1129 q = 1) (hb : d94753 q = 1) : d12957 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1129, d12957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12559 q ha hb
    | true =>
      simp only [d1129, d12957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12536 q ha hb
  have h3 (q : Pattern) (ha : d1130 q = 1) (hb : d94753 q = 1) : d12958 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1130, d12958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1130, d12958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1131 q = 1) (hb : d94753 q = 1) : d12959 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1131, d12959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1131, d12959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1219 q = 1) (hb : d94755 q = 1) : d97900 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1219, d94755, d97900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1219, d94755, d97900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1131 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1142 q = 1) (hb : d94753 q = 1) : d12962 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1142, d12962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12536 q ha hb
    | true =>
      simp only [d1142, d12962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12537 q ha hb
  have h8 (q : Pattern) (ha : d1143 q = 1) (hb : d94753 q = 1) : d12963 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1143, d12963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1143, d12963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1144 q = 1) (hb : d94753 q = 1) : d12964 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1144, d12964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1144, d12964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1145 q = 1) (hb : d94755 q = 1) : d97861 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1145, d94755, d97861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1145, d94755, d97861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1220 q = 1) (hb : d94755 q = 1) : d97901 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1220, d97901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1220, d97901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d1221 q = 1) (hb : d94755 q = 1) : d97902 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1221, d97902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1221, d97902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro12561 (p : Pattern) (ha : d6956 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1131 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6954 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6954, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6954, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5026 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5027 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5027, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d5027, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d6955 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6956 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12562 (p : Pattern) (ha : d6962 p = 1) (hb : d94755 p = 1) : d97908 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1222 q = 1) (hb : d94755 q = 1) : d97903 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1222, d97903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12560 q ha hb
    | true =>
      simp only [d1222, d97903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1223 q = 1) (hb : d94755 q = 1) : d97904 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1223, d97904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1223, d97904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6957 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12561 q ha hb
    | true =>
      simp only [d6957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6958 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6959 q = 1) (hb : d94755 q = 1) : d97905 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6959, d97905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6959, d97905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6960 q = 1) (hb : d94755 q = 1) : d97906 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6960, d97906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6960, d97906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6961 q = 1) (hb : d94755 q = 1) : d97907 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6961, d97907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6961, d97907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6962 q = 1) (hb : d94755 q = 1) : d97908 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6962, d97908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6962, d97908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro12563 (p : Pattern) (ha : d82152 p = 1) (hb : d94755 p = 1) : d97915 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1186 q = 1) (hb : d94755 q = 1) : d97890 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1186, d97890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12554 q ha hb
    | true =>
      simp only [d1186, d97890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12555 q ha hb
  have h2 (q : Pattern) (ha : d1187 q = 1) (hb : d94755 q = 1) : d97891 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1187, d97891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1187, d97891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1188 q = 1) (hb : d94755 q = 1) : d97892 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, d97892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1188, d97892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1189 q = 1) (hb : d94755 q = 1) : d97893 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, d97893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1189, d97893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1196 q = 1) (hb : d94755 q = 1) : d97897 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1196, d97897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12556 q ha hb
    | true =>
      simp only [d1196, d97897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12557 q ha hb
  have h6 (q : Pattern) (ha : d1197 q = 1) (hb : d94755 q = 1) : d97898 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, d97898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1197, d97898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1198 q = 1) (hb : d94755 q = 1) : d97899 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, d97899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1198, d97899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6967 q = 1) (hb : d94755 q = 1) : d97909 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6967, d97909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12562 q ha hb
    | true =>
      simp only [d6967, d97909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12552 q ha hb
  have h9 (q : Pattern) (ha : d82148 q = 1) (hb : d94755 q = 1) : d97910 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82148, d97910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d82148, d97910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6299 q = 1) (hb : d94755 q = 1) : d97870 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6299, d97870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12558 q ha hb
    | true =>
      simp only [d6299, d97870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d6300 q = 1) (hb : d94755 q = 1) : d97911 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6300, d97911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6300, d97911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d82149 q = 1) (hb : d94755 q = 1) : d97912 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82149, d97912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82149, d97912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d82150 q = 1) (hb : d94755 q = 1) : d97913 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82150, d97913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82150, d97913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d82151 q = 1) (hb : d94755 q = 1) : d97914 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82151, d97914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82151, d97914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d82152 q = 1) (hb : d94755 q = 1) : d97915 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82152, d97915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82152, d97915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro12564 (p : Pattern) (ha : d1326 p = 1) (hb : d94755 p = 1) : d97916 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1149 q = 1) (hb : d94755 q = 1) : d97864 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12538 q ha hb
    | true =>
      simp only [d1149, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1150 q = 1) (hb : d94755 q = 1) : d97865 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12539 q ha hb
    | true =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1155 q = 1) (hb : d94755 q = 1) : d97866 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1155, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1156 q = 1) (hb : d94755 q = 1) : d97867 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1156, d97867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1156, d97867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1182 q = 1) (hb : d94755 q = 1) : d97888 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1182, d97888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1182, d97888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1326 q = 1) (hb : d94755 q = 1) : d97916 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1326, d97916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1326, d97916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro12565 (p : Pattern) (ha : d1327 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12539 q ha hb
    | true =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1184 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1327 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro12566 (p : Pattern) (ha : d1332 p = 1) (hb : d94755 p = 1) : d97921 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1149 q = 1) (hb : d94755 q = 1) : d97864 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12538 q ha hb
    | true =>
      simp only [d1149, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1150 q = 1) (hb : d94755 q = 1) : d97865 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12539 q ha hb
    | true =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1155 q = 1) (hb : d94755 q = 1) : d97866 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1155, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1190 q = 1) (hb : d94755 q = 1) : d97894 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1190, d97894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1190, d97894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1191 q = 1) (hb : d94755 q = 1) : d97895 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1191, d97895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1191, d97895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1332 q = 1) (hb : d94755 q = 1) : d97921 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1332, d97921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1332, d97921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro12567 (p : Pattern) (ha : d1333 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12539 q ha hb
    | true =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1193 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1194 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1333 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro12568 (p : Pattern) (ha : d6266 p = 1) (hb : d94755 p = 1) : d97878 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1149 q = 1) (hb : d94755 q = 1) : d97864 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12538 q ha hb
    | true =>
      simp only [d1149, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1150 q = 1) (hb : d94755 q = 1) : d97865 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6254 q = 1) (hb : d94755 q = 1) : d97866 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6254, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6254, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6255 q = 1) (hb : d94755 q = 1) : d97867 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6255, d97867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6255, d97867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6256 q = 1) (hb : d94755 q = 1) : d97868 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6256, d97868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6256, d97868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6266 q = 1) (hb : d94755 q = 1) : d97878 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6266, d97878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6266, d97878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro12569 (p : Pattern) (ha : d6973 p = 1) (hb : d94755 p = 1) : d97925 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1222 q = 1) (hb : d94755 q = 1) : d97903 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1222, d97903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12560 q ha hb
    | true =>
      simp only [d1222, d97903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1223 q = 1) (hb : d94755 q = 1) : d97904 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1223, d97904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1223, d97904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6957 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12561 q ha hb
    | true =>
      simp only [d6957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6958 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6959 q = 1) (hb : d94755 q = 1) : d97905 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6959, d97905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6959, d97905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6960 q = 1) (hb : d94755 q = 1) : d97906 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6960, d97906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6960, d97906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6961 q = 1) (hb : d94755 q = 1) : d97907 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6961, d97907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6961, d97907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6973 q = 1) (hb : d94755 q = 1) : d97925 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6973, d97925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6973, d97925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro12570 (p : Pattern) (ha : d6974 p = 1) (hb : d94755 p = 1) : d97878 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5030 q = 1) (hb : d94755 q = 1) : d97864 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5030, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12551 q ha hb
    | true =>
      simp only [d5030, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5031 q = 1) (hb : d94755 q = 1) : d97865 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5031, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5031, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12539 q ha hb
    | true =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6963 q = 1) (hb : d94755 q = 1) : d97866 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6963, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6963, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6964 q = 1) (hb : d94755 q = 1) : d97867 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6964, d97867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6964, d97867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6965 q = 1) (hb : d94755 q = 1) : d97868 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6965, d97868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6965, d97868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6974 q = 1) (hb : d94755 q = 1) : d97878 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6974, d97878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6974, d97878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro12571 (p : Pattern) (ha : d82157 p = 1) (hb : d94755 p = 1) : d97932 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1186 q = 1) (hb : d94755 q = 1) : d97890 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1186, d97890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12554 q ha hb
    | true =>
      simp only [d1186, d97890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12555 q ha hb
  have h2 (q : Pattern) (ha : d1187 q = 1) (hb : d94755 q = 1) : d97891 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1187, d97891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1187, d97891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1188 q = 1) (hb : d94755 q = 1) : d97892 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, d97892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1188, d97892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1189 q = 1) (hb : d94755 q = 1) : d97893 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, d97893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1189, d97893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1196 q = 1) (hb : d94755 q = 1) : d97897 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1196, d97897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12556 q ha hb
    | true =>
      simp only [d1196, d97897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12557 q ha hb
  have h6 (q : Pattern) (ha : d1197 q = 1) (hb : d94755 q = 1) : d97898 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, d97898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1197, d97898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1198 q = 1) (hb : d94755 q = 1) : d97899 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, d97899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1198, d97899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6967 q = 1) (hb : d94755 q = 1) : d97909 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6967, d97909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12562 q ha hb
    | true =>
      simp only [d6967, d97909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12552 q ha hb
  have h9 (q : Pattern) (ha : d82148 q = 1) (hb : d94755 q = 1) : d97910 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82148, d97910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d82148, d97910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6299 q = 1) (hb : d94755 q = 1) : d97870 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6299, d97870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12558 q ha hb
    | true =>
      simp only [d6299, d97870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d6300 q = 1) (hb : d94755 q = 1) : d97911 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6300, d97911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6300, d97911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d82149 q = 1) (hb : d94755 q = 1) : d97912 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82149, d97912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82149, d97912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d82150 q = 1) (hb : d94755 q = 1) : d97913 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82150, d97913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82150, d97913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d82151 q = 1) (hb : d94755 q = 1) : d97914 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82151, d97914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82151, d97914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d1328 q = 1) (hb : d94755 q = 1) : d97917 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1328, d97917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12564 q ha hb
    | true =>
      simp only [d1328, d97917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12565 q ha hb
  have h16 (q : Pattern) (ha : d1329 q = 1) (hb : d94755 q = 1) : d97918 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1329, d97918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1329, d97918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d1330 q = 1) (hb : d94755 q = 1) : d97919 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1330, d97919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d1330, d97919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d1331 q = 1) (hb : d94755 q = 1) : d97920 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1331, d97920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1331, d97920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d1334 q = 1) (hb : d94755 q = 1) : d97922 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1334, d97922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12566 q ha hb
    | true =>
      simp only [d1334, d97922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12567 q ha hb
  have h20 (q : Pattern) (ha : d1335 q = 1) (hb : d94755 q = 1) : d97923 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1335, d97923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1335, d97923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d1336 q = 1) (hb : d94755 q = 1) : d97924 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1336, d97924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d1336, d97924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d6975 q = 1) (hb : d94755 q = 1) : d97926 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6975, d97926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12569 q ha hb
    | true =>
      simp only [d6975, d97926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12570 q ha hb
  have h23 (q : Pattern) (ha : d82153 q = 1) (hb : d94755 q = 1) : d97927 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82153, d97927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d82153, d97927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d6320 q = 1) (hb : d94755 q = 1) : d97879 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6320, d97879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12568 q ha hb
    | true =>
      simp only [d6320, d97879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d6321 q = 1) (hb : d94755 q = 1) : d97928 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6321, d97928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d6321, d97928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d82154 q = 1) (hb : d94755 q = 1) : d97929 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82154, d97929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d82154, d97929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d82155 q = 1) (hb : d94755 q = 1) : d97930 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82155, d97930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d82155, d97930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d82156 q = 1) (hb : d94755 q = 1) : d97931 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82156, d97931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d82156, d97931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d82157 q = 1) (hb : d94755 q = 1) : d97932 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82157, d97932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d82157, d97932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro12572 (p : Pattern) (ha : d82164 p = 1) (hb : d94755 p = 1) : d97941 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6975 q = 1) (hb : d94755 q = 1) : d97926 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6975, d97926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12569 q ha hb
    | true =>
      simp only [d6975, d97926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12570 q ha hb
  have h2 (q : Pattern) (ha : d82153 q = 1) (hb : d94755 q = 1) : d97927 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82153, d97927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82153, d97927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6320 q = 1) (hb : d94755 q = 1) : d97879 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6320, d97879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12568 q ha hb
    | true =>
      simp only [d6320, d97879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6321 q = 1) (hb : d94755 q = 1) : d97928 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6321, d97928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6321, d97928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82154 q = 1) (hb : d94755 q = 1) : d97929 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82154, d97929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82154, d97929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82162 q = 1) (hb : d94755 q = 1) : d97939 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82162, d97939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82162, d97939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82163 q = 1) (hb : d94755 q = 1) : d97940 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82163, d97940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82163, d97940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82164 q = 1) (hb : d94755 q = 1) : d97941 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82164, d97941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82164, d97941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro12573 (p : Pattern) (ha : d1401 p = 1) (hb : d94753 p = 1) : d6349 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1395 q = 1) : d1395 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1400 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1401 q = 1) (hb : d94753 q = 1) : d6349 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1401, d94753, d6349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1401, d94753, d6349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro12574 (p : Pattern) (ha : d1411 p = 1) (hb : d94753 p = 1) : d13190 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1400 q = 1) : d1400 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1410 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1411 q = 1) (hb : d94753 q = 1) : d13190 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1411, d94753, d13190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1411, d94753, d13190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro12575 (p : Pattern) (ha : d1422 p = 1) (hb : d94755 p = 1) : d97958 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1404 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1412 q = 1) (hb : d94753 q = 1) : d13191 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, d13191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12573 q ha hb
    | true =>
      simp only [d1412, d13191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12574 q ha hb
  have h3 (q : Pattern) (ha : d1413 q = 1) (hb : d94753 q = 1) : d13192 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, d13192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1413, d13192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1414 q = 1) (hb : d94753 q = 1) : d13193 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, d13193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1414, d13193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1415 q = 1) (hb : d94755 q = 1) : d97948 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1415, d94755, d97948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1415, d94755, d97948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1414 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1420 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1420, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1420, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1421 q = 1) (hb : d94755 q = 1) : d97957 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1421, d97957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1421, d97957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1422 q = 1) (hb : d94755 q = 1) : d97958 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1422, d97958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1422, d97958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro12576 (p : Pattern) (ha : d6378 p = 1) (hb : d94755 p = 1) : d97964 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1423 q = 1) (hb : d94755 q = 1) : d97959 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1423, d97959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12575 q ha hb
    | true =>
      simp only [d1423, d97959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1424 q = 1) (hb : d94755 q = 1) : d97960 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1424, d97960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1424, d97960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6375 q = 1) (hb : d94755 q = 1) : d97961 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6375, d97961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6375, d97961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6376 q = 1) (hb : d94755 q = 1) : d97962 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6376, d97962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6376, d97962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6377 q = 1) (hb : d94755 q = 1) : d97963 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6377, d97963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6377, d97963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6378 q = 1) (hb : d94755 q = 1) : d97964 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6378, d97964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6378, d97964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro12577 (p : Pattern) (ha : d1396 p = 1) (hb : d94753 p = 1) : d13156 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1389 q = 1) : d1389 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1395 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1396 q = 1) (hb : d94753 q = 1) : d13156 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1396, d94753, d13156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1396, d94753, d13156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro12578 (p : Pattern) (ha : d1417 p = 1) (hb : d94755 p = 1) : d97950 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1399 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1402 q = 1) (hb : d94753 q = 1) : d13174 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, d13174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12577 q ha hb
    | true =>
      simp only [d1402, d13174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12573 q ha hb
  have h3 (q : Pattern) (ha : d1403 q = 1) (hb : d94753 q = 1) : d13175 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, d13175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1403, d13175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1404 q = 1) (hb : d94753 q = 1) : d13176 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, d13176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1404, d13176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1405 q = 1) (hb : d94755 q = 1) : d97947 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1405, d94755, d97947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1405, d94755, d97947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1404 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1412 q = 1) (hb : d94753 q = 1) : d13191 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, d13191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12573 q ha hb
    | true =>
      simp only [d1412, d13191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12574 q ha hb
  have h8 (q : Pattern) (ha : d1413 q = 1) (hb : d94753 q = 1) : d13192 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, d13192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1413, d13192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1414 q = 1) (hb : d94753 q = 1) : d13193 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, d13193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1414, d13193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1415 q = 1) (hb : d94755 q = 1) : d97948 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1415, d94755, d97948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1415, d94755, d97948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1416 q = 1) (hb : d94755 q = 1) : d97949 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1416, d97949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1416, d97949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d1417 q = 1) (hb : d94755 q = 1) : d97950 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1417, d97950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1417, d97950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro12579 (p : Pattern) (ha : d7002 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1404 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7000 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7000, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7000, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6358 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6359 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6359, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d6359, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d7001 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7002 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12580 (p : Pattern) (ha : d7008 p = 1) (hb : d94755 p = 1) : d97956 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1418 q = 1) (hb : d94755 q = 1) : d97951 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1418, d97951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12578 q ha hb
    | true =>
      simp only [d1418, d97951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1419 q = 1) (hb : d94755 q = 1) : d97952 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1419, d97952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1419, d97952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7003 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12579 q ha hb
    | true =>
      simp only [d7003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7004 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7005 q = 1) (hb : d94755 q = 1) : d97953 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7005, d97953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7005, d97953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7006 q = 1) (hb : d94755 q = 1) : d97954 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7006, d97954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7006, d97954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7007 q = 1) (hb : d94755 q = 1) : d97955 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7007, d97955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7007, d97955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7008 q = 1) (hb : d94755 q = 1) : d97956 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7008, d97956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7008, d97956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro12581 (p : Pattern) (ha : d6361 p = 1) (hb : d94755 p = 1) : d97958 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1404 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1412 q = 1) (hb : d94753 q = 1) : d13191 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, d13191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12573 q ha hb
    | true =>
      simp only [d1412, d13191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12574 q ha hb
  have h3 (q : Pattern) (ha : d1413 q = 1) (hb : d94753 q = 1) : d13192 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, d13192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1413, d13192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1414 q = 1) (hb : d94753 q = 1) : d13193 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, d13193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1414, d13193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1415 q = 1) (hb : d94755 q = 1) : d97948 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1415, d94755, d97948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1415, d94755, d97948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6358 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6359 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6359, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d6359, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d6360 q = 1) (hb : d94755 q = 1) : d97957 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6360, d97957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6360, d97957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d6361 q = 1) (hb : d94755 q = 1) : d97958 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6361, d97958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6361, d97958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro12582 (p : Pattern) (ha : d7012 p = 1) (hb : d94755 p = 1) : d97964 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6362 q = 1) (hb : d94755 q = 1) : d97959 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6362, d97959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12581 q ha hb
    | true =>
      simp only [d6362, d97959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6363 q = 1) (hb : d94755 q = 1) : d97960 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6363, d97960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6363, d97960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1431 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12548 q ha hb
    | true =>
      simp only [d1431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1432 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7009 q = 1) (hb : d94755 q = 1) : d97961 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7009, d97961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7009, d97961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7010 q = 1) (hb : d94755 q = 1) : d97962 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7010, d97962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7010, d97962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7011 q = 1) (hb : d94755 q = 1) : d97963 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7011, d97963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7011, d97963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7012 q = 1) (hb : d94755 q = 1) : d97964 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7012, d97964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7012, d97964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro12583 (p : Pattern) (ha : d82174 p = 1) (hb : d94755 p = 1) : d97972 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7013 q = 1) (hb : d94755 q = 1) : d97965 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7013, d97965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12580 q ha hb
    | true =>
      simp only [d7013, d97965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12582 q ha hb
  have h2 (q : Pattern) (ha : d82170 q = 1) (hb : d94755 q = 1) : d97966 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82170, d97966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82170, d97966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6379 q = 1) (hb : d94755 q = 1) : d97967 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6379, d97967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12576 q ha hb
    | true =>
      simp only [d6379, d97967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6380 q = 1) (hb : d94755 q = 1) : d97968 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6380, d97968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6380, d97968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82171 q = 1) (hb : d94755 q = 1) : d97969 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82171, d97969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82171, d97969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82172 q = 1) (hb : d94755 q = 1) : d97970 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82172, d97970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82172, d97970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82173 q = 1) (hb : d94755 q = 1) : d97971 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82173, d97971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82173, d97971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82174 q = 1) (hb : d94755 q = 1) : d97972 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82174, d97972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82174, d97972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro12584 (p : Pattern) (ha : d82180 p = 1) (hb : d94755 p = 1) : d97978 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1169 q = 1) (hb : d94755 q = 1) : d97876 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1169, d97876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1169, d97876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12542 q ha hb
  have h2 (q : Pattern) (ha : d1170 q = 1) (hb : d94755 q = 1) : d97877 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1170, d97877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1170, d97877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1179 q = 1) (hb : d94755 q = 1) : d97885 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d97885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12542 q ha hb
    | true =>
      simp only [d1179, d97885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12545 q ha hb
  have h4 (q : Pattern) (ha : d1180 q = 1) (hb : d94755 q = 1) : d97886 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d97886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1180, d97886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1181 q = 1) (hb : d94755 q = 1) : d97887 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1181, d97887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1181, d97887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82158 q = 1) (hb : d94755 q = 1) : d97933 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82158, d97933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12563 q ha hb
    | true =>
      simp only [d82158, d97933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12571 q ha hb
  have h7 (q : Pattern) (ha : d6988 q = 1) (hb : d94755 q = 1) : d97935 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6988, d97935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12553 q ha hb
    | true =>
      simp only [d6988, d97935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12546 q ha hb
  have h8 (q : Pattern) (ha : d82159 q = 1) (hb : d94755 q = 1) : d97936 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82159, d97936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82159, d97936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d82160 q = 1) (hb : d94755 q = 1) : d97937 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82160, d97937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d82160, d97937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d82161 q = 1) (hb : d94755 q = 1) : d97938 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82161, d97938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82161, d97938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d82165 q = 1) (hb : d94755 q = 1) : d97942 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82165, d97942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82165, d97942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12572 q ha hb
  have h12 (q : Pattern) (ha : d1371 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12547 q ha hb
  have h13 (q : Pattern) (ha : d82166 q = 1) (hb : d94755 q = 1) : d97943 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82166, d97943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82166, d97943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d82167 q = 1) (hb : d94755 q = 1) : d97944 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82167, d97944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82167, d97944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d82168 q = 1) (hb : d94755 q = 1) : d97945 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82168, d97945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d82168, d97945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d82169 q = 1) (hb : d94755 q = 1) : d97946 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82169, d97946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82169, d97946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d82175 q = 1) (hb : d94755 q = 1) : d97973 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82175, d97973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82175, d97973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12583 q ha hb
  have h18 (q : Pattern) (ha : d1504 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12550 q ha hb
  have h19 (q : Pattern) (ha : d82176 q = 1) (hb : d94755 q = 1) : d97974 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82176, d97974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d82176, d97974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d82177 q = 1) (hb : d94755 q = 1) : d97975 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82177, d97975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d82177, d97975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d82178 q = 1) (hb : d94755 q = 1) : d97976 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82178, d97976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d82178, d97976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d82179 q = 1) (hb : d94755 q = 1) : d97977 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82179, d97977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d82179, d97977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d82180 q = 1) (hb : d94755 q = 1) : d97978 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82180, d97978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d82180, d97978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro12585 (p : Pattern) (ha : d82186 p = 1) (hb : d94755 p = 1) : d97984 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82181 q = 1) (hb : d94755 q = 1) : d97979 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82181, d97979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82181, d97979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12584 q ha hb
  have h2 (q : Pattern) (ha : d82182 q = 1) (hb : d94755 q = 1) : d97980 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82182, d97980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82182, d97980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82183 q = 1) (hb : d94755 q = 1) : d97981 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82183, d97981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82183, d97981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82184 q = 1) (hb : d94755 q = 1) : d97982 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82184, d97982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82184, d97982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82185 q = 1) (hb : d94755 q = 1) : d97983 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82185, d97983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82185, d97983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82186 q = 1) (hb : d94755 q = 1) : d97984 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82186, d97984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82186, d97984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12586 (p : Pattern) (ha : d1589 p = 1) (hb : d94753 p = 1) : d5120 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1586 q = 1) : d1586 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1588 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1589 q = 1) (hb : d94753 q = 1) : d5120 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1589, d94753, d5120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1589, d94753, d5120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro12587 (p : Pattern) (ha : d1602 p = 1) (hb : d94753 p = 1) : d13287 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1588 q = 1) : d1588 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1601 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1602 q = 1) (hb : d94753 q = 1) : d13287 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1602, d94753, d13287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1602, d94753, d13287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro12588 (p : Pattern) (ha : d1609 p = 1) (hb : d94755 p = 1) : d97990 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1592 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1603 q = 1) (hb : d94753 q = 1) : d13288 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1603, d13288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12586 q ha hb
    | true =>
      simp only [d1603, d13288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12587 q ha hb
  have h3 (q : Pattern) (ha : d1604 q = 1) (hb : d94753 q = 1) : d13289 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1604, d13289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1604, d13289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1605 q = 1) (hb : d94753 q = 1) : d13290 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1605, d13290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1605, d13290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1606 q = 1) (hb : d94755 q = 1) : d97988 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1606, d94755, d97988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1606, d94755, d97988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1605 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1607 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1607, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1607, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1608 q = 1) (hb : d94755 q = 1) : d97989 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1608, d97989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1608, d97989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1609 q = 1) (hb : d94755 q = 1) : d97990 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1609, d97990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1609, d97990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro12589 (p : Pattern) (ha : d1613 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1605 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1607 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1607, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1607, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1612 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1613 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro12590 (p : Pattern) (ha : d1619 p = 1) (hb : d94755 p = 1) : d97996 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1610 q = 1) (hb : d94755 q = 1) : d97991 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12588 q ha hb
    | true =>
      simp only [d1610, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1611 q = 1) (hb : d94755 q = 1) : d97992 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12589 q ha hb
    | true =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1616 q = 1) (hb : d94755 q = 1) : d97993 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1616, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1617 q = 1) (hb : d94755 q = 1) : d97994 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1617, d97994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1617, d97994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1618 q = 1) (hb : d94755 q = 1) : d97995 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1618, d97995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1618, d97995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1619 q = 1) (hb : d94755 q = 1) : d97996 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1619, d97996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1619, d97996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro12591 (p : Pattern) (ha : d1623 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12589 q ha hb
    | true =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1622 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1623 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12592 (p : Pattern) (ha : d1629 p = 1) (hb : d94755 p = 1) : d98002 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1624 q = 1) (hb : d94755 q = 1) : d97997 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1624, d97997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12590 q ha hb
    | true =>
      simp only [d1624, d97997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12591 q ha hb
  have h2 (q : Pattern) (ha : d1625 q = 1) (hb : d94755 q = 1) : d97998 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d97998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1625, d97998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1626 q = 1) (hb : d94755 q = 1) : d97999 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d97999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1626, d97999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1627 q = 1) (hb : d94755 q = 1) : d98000 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, d98000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1627, d98000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1628 q = 1) (hb : d94755 q = 1) : d98001 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, d98001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, d98001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1629 q = 1) (hb : d94755 q = 1) : d98002 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1629, d98002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1629, d98002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12593 (p : Pattern) (ha : d1632 p = 1) (hb : d94755 p = 1) : d98005 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1610 q = 1) (hb : d94755 q = 1) : d97991 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12588 q ha hb
    | true =>
      simp only [d1610, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1611 q = 1) (hb : d94755 q = 1) : d97992 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12589 q ha hb
    | true =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1616 q = 1) (hb : d94755 q = 1) : d97993 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1616, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1617 q = 1) (hb : d94755 q = 1) : d97994 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1617, d97994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1617, d97994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1618 q = 1) (hb : d94755 q = 1) : d97995 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1618, d97995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1618, d97995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1632 q = 1) (hb : d94755 q = 1) : d98005 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1632, d98005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1632, d98005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro12594 (p : Pattern) (ha : d1633 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12589 q ha hb
    | true =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1622 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1633 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro12595 (p : Pattern) (ha : d1639 p = 1) (hb : d94755 p = 1) : d98011 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1624 q = 1) (hb : d94755 q = 1) : d97997 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1624, d97997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12590 q ha hb
    | true =>
      simp only [d1624, d97997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12591 q ha hb
  have h2 (q : Pattern) (ha : d1625 q = 1) (hb : d94755 q = 1) : d97998 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d97998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1625, d97998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1626 q = 1) (hb : d94755 q = 1) : d97999 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d97999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1626, d97999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1627 q = 1) (hb : d94755 q = 1) : d98000 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, d98000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1627, d98000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1628 q = 1) (hb : d94755 q = 1) : d98001 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, d98001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, d98001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1634 q = 1) (hb : d94755 q = 1) : d98006 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1634, d98006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12593 q ha hb
    | true =>
      simp only [d1634, d98006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12594 q ha hb
  have h7 (q : Pattern) (ha : d1635 q = 1) (hb : d94755 q = 1) : d98007 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1635, d98007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1635, d98007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1636 q = 1) (hb : d94755 q = 1) : d98008 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1636, d98008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1636, d98008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1637 q = 1) (hb : d94755 q = 1) : d98009 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1637, d98009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1637, d98009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1638 q = 1) (hb : d94755 q = 1) : d98010 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1638, d98010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1638, d98010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1639 q = 1) (hb : d94755 q = 1) : d98011 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1639, d98011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1639, d98011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro12596 (p : Pattern) (ha : d1838 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1827 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12591 q ha hb
    | true =>
      simp only [d1827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1828 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1829 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1830 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1831 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1833 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12594 q ha hb
    | true =>
      simp only [d1833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1834 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1835 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1836 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1837 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1838 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro12597 (p : Pattern) (ha : d1847 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1833 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12594 q ha hb
    | true =>
      simp only [d1833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1834 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1835 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1836 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1837 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1847 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12598 (p : Pattern) (ha : d1907 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1891 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1897 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1897, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1897, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1906 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1907 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro12599 (p : Pattern) (ha : d1974 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1908 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12598 q ha hb
    | true =>
      simp only [d1908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1909 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1971 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1972 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1973 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1974 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro12600 (p : Pattern) (ha : d1980 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1975 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12599 q ha hb
    | true =>
      simp only [d1975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1976 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1977 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1978 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1979 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1980 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12601 (p : Pattern) (ha : d5145 p = 1) (hb : d94755 p = 1) : d97990 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1592 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1603 q = 1) (hb : d94753 q = 1) : d13288 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1603, d13288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12586 q ha hb
    | true =>
      simp only [d1603, d13288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12587 q ha hb
  have h3 (q : Pattern) (ha : d1604 q = 1) (hb : d94753 q = 1) : d13289 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1604, d13289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1604, d13289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1605 q = 1) (hb : d94753 q = 1) : d13290 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1605, d13290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1605, d13290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1606 q = 1) (hb : d94755 q = 1) : d97988 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1606, d94755, d97988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1606, d94755, d97988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5142 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5143 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5143, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d5143, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d5144 q = 1) (hb : d94755 q = 1) : d97989 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d5144, d97989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5144, d97989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d5145 q = 1) (hb : d94755 q = 1) : d97990 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d5145, d97990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5145, d97990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro12602 (p : Pattern) (ha : d7046 p = 1) (hb : d94755 p = 1) : d97996 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5146 q = 1) (hb : d94755 q = 1) : d97991 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5146, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12601 q ha hb
    | true =>
      simp only [d5146, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5147 q = 1) (hb : d94755 q = 1) : d97992 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5147, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5147, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12589 q ha hb
    | true =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7043 q = 1) (hb : d94755 q = 1) : d97993 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7043, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7043, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7044 q = 1) (hb : d94755 q = 1) : d97994 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7044, d97994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7044, d97994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7045 q = 1) (hb : d94755 q = 1) : d97995 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7045, d97995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7045, d97995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7046 q = 1) (hb : d94755 q = 1) : d97996 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7046, d97996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7046, d97996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro12603 (p : Pattern) (ha : d7067 p = 1) (hb : d94755 p = 1) : d98061 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7062 q = 1) (hb : d94755 q = 1) : d97997 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7062, d97997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12602 q ha hb
    | true =>
      simp only [d7062, d97997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12591 q ha hb
  have h2 (q : Pattern) (ha : d7063 q = 1) (hb : d94755 q = 1) : d97998 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7063, d97998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7063, d97998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7064 q = 1) (hb : d94755 q = 1) : d97999 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7064, d97999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7064, d97999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7065 q = 1) (hb : d94755 q = 1) : d98000 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7065, d98000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7065, d98000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7066 q = 1) (hb : d94755 q = 1) : d98001 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7066, d98001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7066, d98001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1827 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12591 q ha hb
    | true =>
      simp only [d1827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1828 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1829 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1830 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1831 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7067 q = 1) (hb : d94755 q = 1) : d98061 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7067, d98061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7067, d98061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro12604 (p : Pattern) (ha : d1644 p = 1) (hb : d94755 p = 1) : d98016 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1610 q = 1) (hb : d94755 q = 1) : d97991 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12588 q ha hb
    | true =>
      simp only [d1610, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1611 q = 1) (hb : d94755 q = 1) : d97992 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12589 q ha hb
    | true =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1616 q = 1) (hb : d94755 q = 1) : d97993 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1616, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1617 q = 1) (hb : d94755 q = 1) : d97994 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1617, d97994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1617, d97994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1643 q = 1) (hb : d94755 q = 1) : d98015 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1643, d98015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1643, d98015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1644 q = 1) (hb : d94755 q = 1) : d98016 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1644, d98016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1644, d98016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro12605 (p : Pattern) (ha : d1646 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12589 q ha hb
    | true =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1645 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1646 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12606 (p : Pattern) (ha : d1653 p = 1) (hb : d94755 p = 1) : d98023 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1610 q = 1) (hb : d94755 q = 1) : d97991 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12588 q ha hb
    | true =>
      simp only [d1610, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1611 q = 1) (hb : d94755 q = 1) : d97992 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12589 q ha hb
    | true =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1616 q = 1) (hb : d94755 q = 1) : d97993 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1616, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1651 q = 1) (hb : d94755 q = 1) : d98021 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1651, d98021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1651, d98021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1652 q = 1) (hb : d94755 q = 1) : d98022 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1652, d98022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1652, d98022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1653 q = 1) (hb : d94755 q = 1) : d98023 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1653, d98023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1653, d98023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro12607 (p : Pattern) (ha : d1656 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12589 q ha hb
    | true =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1654 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1655 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1656 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12608 (p : Pattern) (ha : d6403 p = 1) (hb : d94755 p = 1) : d97996 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1610 q = 1) (hb : d94755 q = 1) : d97991 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12588 q ha hb
    | true =>
      simp only [d1610, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1611 q = 1) (hb : d94755 q = 1) : d97992 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6400 q = 1) (hb : d94755 q = 1) : d97993 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6400, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6400, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6401 q = 1) (hb : d94755 q = 1) : d97994 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6401, d97994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6401, d97994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6402 q = 1) (hb : d94755 q = 1) : d97995 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6402, d97995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6402, d97995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6403 q = 1) (hb : d94755 q = 1) : d97996 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6403, d97996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6403, d97996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12609 (p : Pattern) (ha : d1587 p = 1) (hb : d94753 p = 1) : d13282 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1574 q = 1) : d1574 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1586 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1587 q = 1) (hb : d94753 q = 1) : d13282 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1587, d94753, d13282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1587, d94753, d13282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro12610 (p : Pattern) (ha : d1676 p = 1) (hb : d94755 p = 1) : d98029 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1673 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1590 q = 1) (hb : d94753 q = 1) : d13283 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1590, d13283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12609 q ha hb
    | true =>
      simp only [d1590, d13283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12586 q ha hb
  have h3 (q : Pattern) (ha : d1591 q = 1) (hb : d94753 q = 1) : d13284 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1591, d13284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1591, d13284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1592 q = 1) (hb : d94753 q = 1) : d13285 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1592, d13285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1592, d13285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1674 q = 1) (hb : d94755 q = 1) : d98027 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1674, d94755, d98027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1674, d94755, d98027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1592 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1603 q = 1) (hb : d94753 q = 1) : d13288 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1603, d13288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12586 q ha hb
    | true =>
      simp only [d1603, d13288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12587 q ha hb
  have h8 (q : Pattern) (ha : d1604 q = 1) (hb : d94753 q = 1) : d13289 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1604, d13289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1604, d13289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1605 q = 1) (hb : d94753 q = 1) : d13290 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1605, d13290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1605, d13290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1606 q = 1) (hb : d94755 q = 1) : d97988 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1606, d94755, d97988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1606, d94755, d97988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1675 q = 1) (hb : d94755 q = 1) : d98028 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1675, d98028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1675, d98028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d1676 q = 1) (hb : d94755 q = 1) : d98029 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1676, d98029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1676, d98029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro12611 (p : Pattern) (ha : d7036 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1592 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7034 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7034, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7034, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5142 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5143 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5143, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d5143, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d7035 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7036 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12612 (p : Pattern) (ha : d7042 p = 1) (hb : d94755 p = 1) : d98035 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1677 q = 1) (hb : d94755 q = 1) : d98030 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1677, d98030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12610 q ha hb
    | true =>
      simp only [d1677, d98030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1678 q = 1) (hb : d94755 q = 1) : d98031 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1678, d98031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1678, d98031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7037 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12611 q ha hb
    | true =>
      simp only [d7037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7038 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7039 q = 1) (hb : d94755 q = 1) : d98032 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7039, d98032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7039, d98032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7040 q = 1) (hb : d94755 q = 1) : d98033 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7040, d98033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7040, d98033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7041 q = 1) (hb : d94755 q = 1) : d98034 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7041, d98034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7041, d98034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7042 q = 1) (hb : d94755 q = 1) : d98035 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7042, d98035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7042, d98035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro12613 (p : Pattern) (ha : d82194 p = 1) (hb : d94755 p = 1) : d98042 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1647 q = 1) (hb : d94755 q = 1) : d98017 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1647, d98017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12604 q ha hb
    | true =>
      simp only [d1647, d98017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12605 q ha hb
  have h2 (q : Pattern) (ha : d1648 q = 1) (hb : d94755 q = 1) : d98018 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1648, d98018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1648, d98018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1649 q = 1) (hb : d94755 q = 1) : d98019 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, d98019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1649, d98019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1650 q = 1) (hb : d94755 q = 1) : d98020 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, d98020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1650, d98020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1657 q = 1) (hb : d94755 q = 1) : d98024 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1657, d98024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12606 q ha hb
    | true =>
      simp only [d1657, d98024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12607 q ha hb
  have h6 (q : Pattern) (ha : d1658 q = 1) (hb : d94755 q = 1) : d98025 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1658, d98025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1658, d98025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1659 q = 1) (hb : d94755 q = 1) : d98026 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, d98026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1659, d98026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7047 q = 1) (hb : d94755 q = 1) : d98036 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7047, d98036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12612 q ha hb
    | true =>
      simp only [d7047, d98036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12602 q ha hb
  have h9 (q : Pattern) (ha : d82190 q = 1) (hb : d94755 q = 1) : d98037 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82190, d98037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d82190, d98037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6445 q = 1) (hb : d94755 q = 1) : d97997 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6445, d97997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12608 q ha hb
    | true =>
      simp only [d6445, d97997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d6446 q = 1) (hb : d94755 q = 1) : d98038 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6446, d98038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6446, d98038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d82191 q = 1) (hb : d94755 q = 1) : d98039 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82191, d98039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82191, d98039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d82192 q = 1) (hb : d94755 q = 1) : d98040 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82192, d98040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82192, d98040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d82193 q = 1) (hb : d94755 q = 1) : d98041 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82193, d98041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82193, d98041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d82194 q = 1) (hb : d94755 q = 1) : d98042 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82194, d98042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82194, d98042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro12614 (p : Pattern) (ha : d1803 p = 1) (hb : d94755 p = 1) : d98043 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1610 q = 1) (hb : d94755 q = 1) : d97991 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12588 q ha hb
    | true =>
      simp only [d1610, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1611 q = 1) (hb : d94755 q = 1) : d97992 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12589 q ha hb
    | true =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1616 q = 1) (hb : d94755 q = 1) : d97993 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1616, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1617 q = 1) (hb : d94755 q = 1) : d97994 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1617, d97994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1617, d97994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1643 q = 1) (hb : d94755 q = 1) : d98015 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1643, d98015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1643, d98015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1803 q = 1) (hb : d94755 q = 1) : d98043 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1803, d98043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1803, d98043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro12615 (p : Pattern) (ha : d1804 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12589 q ha hb
    | true =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1645 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1804 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro12616 (p : Pattern) (ha : d1809 p = 1) (hb : d94755 p = 1) : d98048 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1610 q = 1) (hb : d94755 q = 1) : d97991 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12588 q ha hb
    | true =>
      simp only [d1610, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1611 q = 1) (hb : d94755 q = 1) : d97992 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12589 q ha hb
    | true =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1616 q = 1) (hb : d94755 q = 1) : d97993 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1616, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1651 q = 1) (hb : d94755 q = 1) : d98021 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1651, d98021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1651, d98021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1652 q = 1) (hb : d94755 q = 1) : d98022 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1652, d98022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1652, d98022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1809 q = 1) (hb : d94755 q = 1) : d98048 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1809, d98048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1809, d98048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro12617 (p : Pattern) (ha : d1810 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12589 q ha hb
    | true =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1654 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1655 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1810 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro12618 (p : Pattern) (ha : d6412 p = 1) (hb : d94755 p = 1) : d98005 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1610 q = 1) (hb : d94755 q = 1) : d97991 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12588 q ha hb
    | true =>
      simp only [d1610, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1611 q = 1) (hb : d94755 q = 1) : d97992 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6400 q = 1) (hb : d94755 q = 1) : d97993 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6400, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6400, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6401 q = 1) (hb : d94755 q = 1) : d97994 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6401, d97994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6401, d97994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6402 q = 1) (hb : d94755 q = 1) : d97995 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6402, d97995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6402, d97995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6412 q = 1) (hb : d94755 q = 1) : d98005 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6412, d98005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6412, d98005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro12619 (p : Pattern) (ha : d7053 p = 1) (hb : d94755 p = 1) : d98052 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1677 q = 1) (hb : d94755 q = 1) : d98030 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1677, d98030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12610 q ha hb
    | true =>
      simp only [d1677, d98030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1678 q = 1) (hb : d94755 q = 1) : d98031 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1678, d98031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1678, d98031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7037 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12611 q ha hb
    | true =>
      simp only [d7037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7038 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7039 q = 1) (hb : d94755 q = 1) : d98032 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7039, d98032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7039, d98032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7040 q = 1) (hb : d94755 q = 1) : d98033 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7040, d98033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7040, d98033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7041 q = 1) (hb : d94755 q = 1) : d98034 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7041, d98034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7041, d98034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7053 q = 1) (hb : d94755 q = 1) : d98052 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7053, d98052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7053, d98052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro12620 (p : Pattern) (ha : d7054 p = 1) (hb : d94755 p = 1) : d98005 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5146 q = 1) (hb : d94755 q = 1) : d97991 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5146, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12601 q ha hb
    | true =>
      simp only [d5146, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5147 q = 1) (hb : d94755 q = 1) : d97992 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5147, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5147, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12589 q ha hb
    | true =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7043 q = 1) (hb : d94755 q = 1) : d97993 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7043, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7043, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7044 q = 1) (hb : d94755 q = 1) : d97994 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7044, d97994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7044, d97994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7045 q = 1) (hb : d94755 q = 1) : d97995 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7045, d97995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7045, d97995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7054 q = 1) (hb : d94755 q = 1) : d98005 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7054, d98005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7054, d98005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro12621 (p : Pattern) (ha : d82199 p = 1) (hb : d94755 p = 1) : d98059 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1647 q = 1) (hb : d94755 q = 1) : d98017 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1647, d98017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12604 q ha hb
    | true =>
      simp only [d1647, d98017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12605 q ha hb
  have h2 (q : Pattern) (ha : d1648 q = 1) (hb : d94755 q = 1) : d98018 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1648, d98018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1648, d98018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1649 q = 1) (hb : d94755 q = 1) : d98019 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, d98019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1649, d98019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1650 q = 1) (hb : d94755 q = 1) : d98020 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, d98020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1650, d98020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1657 q = 1) (hb : d94755 q = 1) : d98024 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1657, d98024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12606 q ha hb
    | true =>
      simp only [d1657, d98024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12607 q ha hb
  have h6 (q : Pattern) (ha : d1658 q = 1) (hb : d94755 q = 1) : d98025 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1658, d98025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1658, d98025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1659 q = 1) (hb : d94755 q = 1) : d98026 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, d98026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1659, d98026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7047 q = 1) (hb : d94755 q = 1) : d98036 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7047, d98036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12612 q ha hb
    | true =>
      simp only [d7047, d98036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12602 q ha hb
  have h9 (q : Pattern) (ha : d82190 q = 1) (hb : d94755 q = 1) : d98037 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82190, d98037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d82190, d98037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6445 q = 1) (hb : d94755 q = 1) : d97997 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6445, d97997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12608 q ha hb
    | true =>
      simp only [d6445, d97997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d6446 q = 1) (hb : d94755 q = 1) : d98038 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6446, d98038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6446, d98038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d82191 q = 1) (hb : d94755 q = 1) : d98039 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82191, d98039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82191, d98039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d82192 q = 1) (hb : d94755 q = 1) : d98040 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82192, d98040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82192, d98040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d82193 q = 1) (hb : d94755 q = 1) : d98041 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82193, d98041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82193, d98041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d1805 q = 1) (hb : d94755 q = 1) : d98044 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1805, d98044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12614 q ha hb
    | true =>
      simp only [d1805, d98044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12615 q ha hb
  have h16 (q : Pattern) (ha : d1806 q = 1) (hb : d94755 q = 1) : d98045 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1806, d98045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1806, d98045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d1807 q = 1) (hb : d94755 q = 1) : d98046 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1807, d98046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d1807, d98046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d1808 q = 1) (hb : d94755 q = 1) : d98047 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1808, d98047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1808, d98047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d1811 q = 1) (hb : d94755 q = 1) : d98049 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1811, d98049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12616 q ha hb
    | true =>
      simp only [d1811, d98049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12617 q ha hb
  have h20 (q : Pattern) (ha : d1812 q = 1) (hb : d94755 q = 1) : d98050 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1812, d98050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1812, d98050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d1813 q = 1) (hb : d94755 q = 1) : d98051 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1813, d98051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d1813, d98051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d7055 q = 1) (hb : d94755 q = 1) : d98053 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7055, d98053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12619 q ha hb
    | true =>
      simp only [d7055, d98053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12620 q ha hb
  have h23 (q : Pattern) (ha : d82195 q = 1) (hb : d94755 q = 1) : d98054 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82195, d98054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d82195, d98054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d6466 q = 1) (hb : d94755 q = 1) : d98006 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6466, d98006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12618 q ha hb
    | true =>
      simp only [d6466, d98006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d6467 q = 1) (hb : d94755 q = 1) : d98055 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6467, d98055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d6467, d98055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d82196 q = 1) (hb : d94755 q = 1) : d98056 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82196, d98056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d82196, d98056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d82197 q = 1) (hb : d94755 q = 1) : d98057 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82197, d98057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d82197, d98057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d82198 q = 1) (hb : d94755 q = 1) : d98058 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82198, d98058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d82198, d98058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d82199 q = 1) (hb : d94755 q = 1) : d98059 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82199, d98059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d82199, d98059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro12622 (p : Pattern) (ha : d82206 p = 1) (hb : d94755 p = 1) : d98068 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7055 q = 1) (hb : d94755 q = 1) : d98053 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7055, d98053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12619 q ha hb
    | true =>
      simp only [d7055, d98053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12620 q ha hb
  have h2 (q : Pattern) (ha : d82195 q = 1) (hb : d94755 q = 1) : d98054 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82195, d98054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82195, d98054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6466 q = 1) (hb : d94755 q = 1) : d98006 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6466, d98006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12618 q ha hb
    | true =>
      simp only [d6466, d98006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6467 q = 1) (hb : d94755 q = 1) : d98055 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6467, d98055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6467, d98055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82196 q = 1) (hb : d94755 q = 1) : d98056 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82196, d98056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82196, d98056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82204 q = 1) (hb : d94755 q = 1) : d98066 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82204, d98066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82204, d98066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82205 q = 1) (hb : d94755 q = 1) : d98067 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82205, d98067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82205, d98067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82206 q = 1) (hb : d94755 q = 1) : d98068 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82206, d98068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82206, d98068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro12623 (p : Pattern) (ha : d1878 p = 1) (hb : d94753 p = 1) : d6495 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1872 q = 1) : d1872 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1877 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1878 q = 1) (hb : d94753 q = 1) : d6495 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1878, d94753, d6495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1878, d94753, d6495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro12624 (p : Pattern) (ha : d1888 p = 1) (hb : d94753 p = 1) : d13516 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1877 q = 1) : d1877 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1887 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1888 q = 1) (hb : d94753 q = 1) : d13516 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1888, d94753, d13516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1888, d94753, d13516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro12625 (p : Pattern) (ha : d1899 p = 1) (hb : d94755 p = 1) : d98085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1881 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1889 q = 1) (hb : d94753 q = 1) : d13517 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, d13517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12623 q ha hb
    | true =>
      simp only [d1889, d13517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12624 q ha hb
  have h3 (q : Pattern) (ha : d1890 q = 1) (hb : d94753 q = 1) : d13518 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, d13518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1890, d13518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1891 q = 1) (hb : d94753 q = 1) : d13519 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, d13519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1891, d13519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1892 q = 1) (hb : d94755 q = 1) : d98075 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1892, d94755, d98075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1892, d94755, d98075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1891 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1897 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1897, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1897, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1898 q = 1) (hb : d94755 q = 1) : d98084 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1898, d98084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1898, d98084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1899 q = 1) (hb : d94755 q = 1) : d98085 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1899, d98085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1899, d98085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro12626 (p : Pattern) (ha : d6524 p = 1) (hb : d94755 p = 1) : d98091 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1900 q = 1) (hb : d94755 q = 1) : d98086 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1900, d98086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12625 q ha hb
    | true =>
      simp only [d1900, d98086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1901 q = 1) (hb : d94755 q = 1) : d98087 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1901, d98087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1901, d98087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6521 q = 1) (hb : d94755 q = 1) : d98088 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6521, d98088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6521, d98088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6522 q = 1) (hb : d94755 q = 1) : d98089 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6522, d98089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6522, d98089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6523 q = 1) (hb : d94755 q = 1) : d98090 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6523, d98090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6523, d98090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6524 q = 1) (hb : d94755 q = 1) : d98091 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6524, d98091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6524, d98091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro12627 (p : Pattern) (ha : d1873 p = 1) (hb : d94753 p = 1) : d13482 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1866 q = 1) : d1866 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1872 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1873 q = 1) (hb : d94753 q = 1) : d13482 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1873, d94753, d13482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1873, d94753, d13482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro12628 (p : Pattern) (ha : d1894 p = 1) (hb : d94755 p = 1) : d98077 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1876 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1879 q = 1) (hb : d94753 q = 1) : d13500 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, d13500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12627 q ha hb
    | true =>
      simp only [d1879, d13500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12623 q ha hb
  have h3 (q : Pattern) (ha : d1880 q = 1) (hb : d94753 q = 1) : d13501 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, d13501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1880, d13501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1881 q = 1) (hb : d94753 q = 1) : d13502 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, d13502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1881, d13502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1882 q = 1) (hb : d94755 q = 1) : d98074 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1882, d94755, d98074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1882, d94755, d98074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1881 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1889 q = 1) (hb : d94753 q = 1) : d13517 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, d13517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12623 q ha hb
    | true =>
      simp only [d1889, d13517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12624 q ha hb
  have h8 (q : Pattern) (ha : d1890 q = 1) (hb : d94753 q = 1) : d13518 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, d13518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1890, d13518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1891 q = 1) (hb : d94753 q = 1) : d13519 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, d13519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1891, d13519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1892 q = 1) (hb : d94755 q = 1) : d98075 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1892, d94755, d98075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1892, d94755, d98075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1893 q = 1) (hb : d94755 q = 1) : d98076 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1893, d98076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1893, d98076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d1894 q = 1) (hb : d94755 q = 1) : d98077 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1894, d98077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1894, d98077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro12629 (p : Pattern) (ha : d7082 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1881 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7080 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7080, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7080, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6504 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6505 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6505, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d6505, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d7081 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7082 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12630 (p : Pattern) (ha : d7088 p = 1) (hb : d94755 p = 1) : d98083 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1895 q = 1) (hb : d94755 q = 1) : d98078 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1895, d98078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12628 q ha hb
    | true =>
      simp only [d1895, d98078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1896 q = 1) (hb : d94755 q = 1) : d98079 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1896, d98079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1896, d98079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7083 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12629 q ha hb
    | true =>
      simp only [d7083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7084 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7085 q = 1) (hb : d94755 q = 1) : d98080 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7085, d98080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7085, d98080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7086 q = 1) (hb : d94755 q = 1) : d98081 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7086, d98081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7086, d98081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7087 q = 1) (hb : d94755 q = 1) : d98082 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7087, d98082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7087, d98082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7088 q = 1) (hb : d94755 q = 1) : d98083 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7088, d98083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7088, d98083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro12631 (p : Pattern) (ha : d6507 p = 1) (hb : d94755 p = 1) : d98085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1881 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1889 q = 1) (hb : d94753 q = 1) : d13517 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, d13517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12623 q ha hb
    | true =>
      simp only [d1889, d13517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12624 q ha hb
  have h3 (q : Pattern) (ha : d1890 q = 1) (hb : d94753 q = 1) : d13518 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, d13518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1890, d13518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1891 q = 1) (hb : d94753 q = 1) : d13519 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, d13519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1891, d13519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1892 q = 1) (hb : d94755 q = 1) : d98075 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1892, d94755, d98075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1892, d94755, d98075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6504 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6505 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6505, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d6505, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d6506 q = 1) (hb : d94755 q = 1) : d98084 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6506, d98084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6506, d98084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d6507 q = 1) (hb : d94755 q = 1) : d98085 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6507, d98085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6507, d98085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro12632 (p : Pattern) (ha : d7092 p = 1) (hb : d94755 p = 1) : d98091 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6508 q = 1) (hb : d94755 q = 1) : d98086 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6508, d98086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12631 q ha hb
    | true =>
      simp only [d6508, d98086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6509 q = 1) (hb : d94755 q = 1) : d98087 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6509, d98087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6509, d98087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1908 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12598 q ha hb
    | true =>
      simp only [d1908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1909 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7089 q = 1) (hb : d94755 q = 1) : d98088 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7089, d98088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7089, d98088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7090 q = 1) (hb : d94755 q = 1) : d98089 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7090, d98089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7090, d98089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7091 q = 1) (hb : d94755 q = 1) : d98090 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7091, d98090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7091, d98090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7092 q = 1) (hb : d94755 q = 1) : d98091 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7092, d98091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7092, d98091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro12633 (p : Pattern) (ha : d82216 p = 1) (hb : d94755 p = 1) : d98099 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7093 q = 1) (hb : d94755 q = 1) : d98092 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7093, d98092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12630 q ha hb
    | true =>
      simp only [d7093, d98092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12632 q ha hb
  have h2 (q : Pattern) (ha : d82212 q = 1) (hb : d94755 q = 1) : d98093 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82212, d98093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82212, d98093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6525 q = 1) (hb : d94755 q = 1) : d98094 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6525, d98094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12626 q ha hb
    | true =>
      simp only [d6525, d98094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6526 q = 1) (hb : d94755 q = 1) : d98095 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6526, d98095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6526, d98095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82213 q = 1) (hb : d94755 q = 1) : d98096 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82213, d98096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82213, d98096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82214 q = 1) (hb : d94755 q = 1) : d98097 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82214, d98097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82214, d98097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82215 q = 1) (hb : d94755 q = 1) : d98098 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82215, d98098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82215, d98098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82216 q = 1) (hb : d94755 q = 1) : d98099 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82216, d98099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82216, d98099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro12634 (p : Pattern) (ha : d82222 p = 1) (hb : d94755 p = 1) : d98105 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1630 q = 1) (hb : d94755 q = 1) : d98003 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1630, d98003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1630, d98003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12592 q ha hb
  have h2 (q : Pattern) (ha : d1631 q = 1) (hb : d94755 q = 1) : d98004 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1631, d98004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1631, d98004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1640 q = 1) (hb : d94755 q = 1) : d98012 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d98012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12592 q ha hb
    | true =>
      simp only [d1640, d98012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12595 q ha hb
  have h4 (q : Pattern) (ha : d1641 q = 1) (hb : d94755 q = 1) : d98013 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d98013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1641, d98013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1642 q = 1) (hb : d94755 q = 1) : d98014 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1642, d98014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1642, d98014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82200 q = 1) (hb : d94755 q = 1) : d98060 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82200, d98060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12613 q ha hb
    | true =>
      simp only [d82200, d98060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12621 q ha hb
  have h7 (q : Pattern) (ha : d7068 q = 1) (hb : d94755 q = 1) : d98062 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7068, d98062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12603 q ha hb
    | true =>
      simp only [d7068, d98062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12596 q ha hb
  have h8 (q : Pattern) (ha : d82201 q = 1) (hb : d94755 q = 1) : d98063 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82201, d98063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82201, d98063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d82202 q = 1) (hb : d94755 q = 1) : d98064 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82202, d98064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d82202, d98064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d82203 q = 1) (hb : d94755 q = 1) : d98065 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82203, d98065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82203, d98065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d82207 q = 1) (hb : d94755 q = 1) : d98069 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82207, d98069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82207, d98069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12622 q ha hb
  have h12 (q : Pattern) (ha : d1848 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12597 q ha hb
  have h13 (q : Pattern) (ha : d82208 q = 1) (hb : d94755 q = 1) : d98070 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82208, d98070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82208, d98070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d82209 q = 1) (hb : d94755 q = 1) : d98071 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82209, d98071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82209, d98071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d82210 q = 1) (hb : d94755 q = 1) : d98072 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82210, d98072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d82210, d98072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d82211 q = 1) (hb : d94755 q = 1) : d98073 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82211, d98073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82211, d98073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d82217 q = 1) (hb : d94755 q = 1) : d98100 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82217, d98100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82217, d98100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12633 q ha hb
  have h18 (q : Pattern) (ha : d1981 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12600 q ha hb
  have h19 (q : Pattern) (ha : d82218 q = 1) (hb : d94755 q = 1) : d98101 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82218, d98101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d82218, d98101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d82219 q = 1) (hb : d94755 q = 1) : d98102 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82219, d98102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d82219, d98102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d82220 q = 1) (hb : d94755 q = 1) : d98103 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82220, d98103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d82220, d98103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d82221 q = 1) (hb : d94755 q = 1) : d98104 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82221, d98104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d82221, d98104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d82222 q = 1) (hb : d94755 q = 1) : d98105 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82222, d98105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d82222, d98105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro12635 (p : Pattern) (ha : d82228 p = 1) (hb : d94755 p = 1) : d98111 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82223 q = 1) (hb : d94755 q = 1) : d98106 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82223, d98106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82223, d98106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12634 q ha hb
  have h2 (q : Pattern) (ha : d82224 q = 1) (hb : d94755 q = 1) : d98107 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82224, d98107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82224, d98107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82225 q = 1) (hb : d94755 q = 1) : d98108 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82225, d98108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82225, d98108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82226 q = 1) (hb : d94755 q = 1) : d98109 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82226, d98109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82226, d98109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82227 q = 1) (hb : d94755 q = 1) : d98110 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82227, d98110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82227, d98110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82228 q = 1) (hb : d94755 q = 1) : d98111 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82228, d98111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82228, d98111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12636 (p : Pattern) (ha : d2072 p = 1) (hb : d94753 p = 1) : d5237 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2069 q = 1) : d2069 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2071 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2072 q = 1) (hb : d94753 q = 1) : d5237 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d2072, d94753, d5237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2072, d94753, d5237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro12637 (p : Pattern) (ha : d2085 p = 1) (hb : d94753 p = 1) : d13614 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2071 q = 1) : d2071 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2084 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2085 q = 1) (hb : d94753 q = 1) : d13614 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d2085, d94753, d13614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2085, d94753, d13614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro12638 (p : Pattern) (ha : d2092 p = 1) (hb : d94755 p = 1) : d98118 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2075 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2086 q = 1) (hb : d94753 q = 1) : d13615 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2086, d13615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12636 q ha hb
    | true =>
      simp only [d2086, d13615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12637 q ha hb
  have h3 (q : Pattern) (ha : d2087 q = 1) (hb : d94753 q = 1) : d13616 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2087, d13616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2087, d13616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2088 q = 1) (hb : d94753 q = 1) : d13617 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2088, d13617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2088, d13617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2089 q = 1) (hb : d94755 q = 1) : d98116 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2089, d94755, d98116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2089, d94755, d98116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d2088 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2090 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2090, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d2090, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d2091 q = 1) (hb : d94755 q = 1) : d98117 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2091, d98117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2091, d98117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2092 q = 1) (hb : d94755 q = 1) : d98118 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2092, d98118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2092, d98118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro12639 (p : Pattern) (ha : d2096 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2088 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2090 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2090, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2090, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2095 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2096 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro12640 (p : Pattern) (ha : d2102 p = 1) (hb : d94755 p = 1) : d98124 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2093 q = 1) (hb : d94755 q = 1) : d98119 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12638 q ha hb
    | true =>
      simp only [d2093, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2094 q = 1) (hb : d94755 q = 1) : d98120 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12639 q ha hb
    | true =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2099 q = 1) (hb : d94755 q = 1) : d98121 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2099, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2100 q = 1) (hb : d94755 q = 1) : d98122 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2100, d98122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2100, d98122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2101 q = 1) (hb : d94755 q = 1) : d98123 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2101, d98123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2101, d98123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2102 q = 1) (hb : d94755 q = 1) : d98124 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2102, d98124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2102, d98124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro12641 (p : Pattern) (ha : d2106 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12639 q ha hb
    | true =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2104 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2105 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2106 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12642 (p : Pattern) (ha : d2112 p = 1) (hb : d94755 p = 1) : d98130 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2107 q = 1) (hb : d94755 q = 1) : d98125 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2107, d98125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12640 q ha hb
    | true =>
      simp only [d2107, d98125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12641 q ha hb
  have h2 (q : Pattern) (ha : d2108 q = 1) (hb : d94755 q = 1) : d98126 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d98126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2108, d98126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2109 q = 1) (hb : d94755 q = 1) : d98127 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d98127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2109, d98127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2110 q = 1) (hb : d94755 q = 1) : d98128 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, d98128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2110, d98128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2111 q = 1) (hb : d94755 q = 1) : d98129 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, d98129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, d98129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2112 q = 1) (hb : d94755 q = 1) : d98130 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2112, d98130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2112, d98130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12643 (p : Pattern) (ha : d2115 p = 1) (hb : d94755 p = 1) : d98133 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2093 q = 1) (hb : d94755 q = 1) : d98119 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12638 q ha hb
    | true =>
      simp only [d2093, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2094 q = 1) (hb : d94755 q = 1) : d98120 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12639 q ha hb
    | true =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2099 q = 1) (hb : d94755 q = 1) : d98121 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2099, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2100 q = 1) (hb : d94755 q = 1) : d98122 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2100, d98122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2100, d98122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2101 q = 1) (hb : d94755 q = 1) : d98123 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2101, d98123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2101, d98123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2115 q = 1) (hb : d94755 q = 1) : d98133 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2115, d98133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2115, d98133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro12644 (p : Pattern) (ha : d2116 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12639 q ha hb
    | true =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2104 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2105 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2116 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro12645 (p : Pattern) (ha : d2122 p = 1) (hb : d94755 p = 1) : d98139 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2107 q = 1) (hb : d94755 q = 1) : d98125 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2107, d98125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12640 q ha hb
    | true =>
      simp only [d2107, d98125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12641 q ha hb
  have h2 (q : Pattern) (ha : d2108 q = 1) (hb : d94755 q = 1) : d98126 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d98126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2108, d98126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2109 q = 1) (hb : d94755 q = 1) : d98127 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d98127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2109, d98127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2110 q = 1) (hb : d94755 q = 1) : d98128 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, d98128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2110, d98128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2111 q = 1) (hb : d94755 q = 1) : d98129 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, d98129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, d98129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2117 q = 1) (hb : d94755 q = 1) : d98134 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2117, d98134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12643 q ha hb
    | true =>
      simp only [d2117, d98134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12644 q ha hb
  have h7 (q : Pattern) (ha : d2118 q = 1) (hb : d94755 q = 1) : d98135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2118, d98135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2118, d98135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2119 q = 1) (hb : d94755 q = 1) : d98136 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2119, d98136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2119, d98136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2120 q = 1) (hb : d94755 q = 1) : d98137 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2120, d98137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2120, d98137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2121 q = 1) (hb : d94755 q = 1) : d98138 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2121, d98138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2121, d98138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2122 q = 1) (hb : d94755 q = 1) : d98139 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2122, d98139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2122, d98139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro12646 (p : Pattern) (ha : d2316 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2305 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12641 q ha hb
    | true =>
      simp only [d2305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2306 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2307 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2308 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2309 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2311 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12644 q ha hb
    | true =>
      simp only [d2311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2312 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2313 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2314 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2315 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2316 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro12647 (p : Pattern) (ha : d2325 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2311 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12644 q ha hb
    | true =>
      simp only [d2311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2312 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2313 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2314 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2315 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2325 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12648 (p : Pattern) (ha : d2385 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2369 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2375 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2375, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2375, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2384 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2385 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro12649 (p : Pattern) (ha : d2452 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2386 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12648 q ha hb
    | true =>
      simp only [d2386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2387 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2449 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2450 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2451 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2452 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro12650 (p : Pattern) (ha : d2458 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2453 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12649 q ha hb
    | true =>
      simp only [d2453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2454 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2455 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2456 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2457 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2458 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12651 (p : Pattern) (ha : d5258 p = 1) (hb : d94755 p = 1) : d98118 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2075 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2086 q = 1) (hb : d94753 q = 1) : d13615 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2086, d13615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12636 q ha hb
    | true =>
      simp only [d2086, d13615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12637 q ha hb
  have h3 (q : Pattern) (ha : d2087 q = 1) (hb : d94753 q = 1) : d13616 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2087, d13616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2087, d13616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2088 q = 1) (hb : d94753 q = 1) : d13617 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2088, d13617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2088, d13617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2089 q = 1) (hb : d94755 q = 1) : d98116 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2089, d94755, d98116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2089, d94755, d98116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5255 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5256 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5256, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d5256, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d5257 q = 1) (hb : d94755 q = 1) : d98117 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d5257, d98117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5257, d98117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d5258 q = 1) (hb : d94755 q = 1) : d98118 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d5258, d98118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5258, d98118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro12652 (p : Pattern) (ha : d7127 p = 1) (hb : d94755 p = 1) : d98124 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5259 q = 1) (hb : d94755 q = 1) : d98119 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5259, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12651 q ha hb
    | true =>
      simp only [d5259, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5260 q = 1) (hb : d94755 q = 1) : d98120 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5260, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5260, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12639 q ha hb
    | true =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7124 q = 1) (hb : d94755 q = 1) : d98121 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7124, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7124, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7125 q = 1) (hb : d94755 q = 1) : d98122 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7125, d98122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7125, d98122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7126 q = 1) (hb : d94755 q = 1) : d98123 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7126, d98123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7126, d98123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7127 q = 1) (hb : d94755 q = 1) : d98124 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7127, d98124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7127, d98124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro12653 (p : Pattern) (ha : d7148 p = 1) (hb : d94755 p = 1) : d98189 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7143 q = 1) (hb : d94755 q = 1) : d98125 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7143, d98125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12652 q ha hb
    | true =>
      simp only [d7143, d98125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12641 q ha hb
  have h2 (q : Pattern) (ha : d7144 q = 1) (hb : d94755 q = 1) : d98126 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7144, d98126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7144, d98126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7145 q = 1) (hb : d94755 q = 1) : d98127 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7145, d98127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7145, d98127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7146 q = 1) (hb : d94755 q = 1) : d98128 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7146, d98128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7146, d98128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7147 q = 1) (hb : d94755 q = 1) : d98129 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7147, d98129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7147, d98129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2305 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12641 q ha hb
    | true =>
      simp only [d2305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2306 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2307 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2308 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2309 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7148 q = 1) (hb : d94755 q = 1) : d98189 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7148, d98189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7148, d98189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro12654 (p : Pattern) (ha : d2127 p = 1) (hb : d94755 p = 1) : d98144 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2093 q = 1) (hb : d94755 q = 1) : d98119 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12638 q ha hb
    | true =>
      simp only [d2093, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2094 q = 1) (hb : d94755 q = 1) : d98120 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12639 q ha hb
    | true =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2099 q = 1) (hb : d94755 q = 1) : d98121 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2099, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2100 q = 1) (hb : d94755 q = 1) : d98122 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2100, d98122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2100, d98122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2126 q = 1) (hb : d94755 q = 1) : d98143 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2126, d98143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2126, d98143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2127 q = 1) (hb : d94755 q = 1) : d98144 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2127, d98144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2127, d98144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro12655 (p : Pattern) (ha : d2129 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12639 q ha hb
    | true =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2104 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2128 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2129 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12656 (p : Pattern) (ha : d2136 p = 1) (hb : d94755 p = 1) : d98151 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2093 q = 1) (hb : d94755 q = 1) : d98119 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12638 q ha hb
    | true =>
      simp only [d2093, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2094 q = 1) (hb : d94755 q = 1) : d98120 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12639 q ha hb
    | true =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2099 q = 1) (hb : d94755 q = 1) : d98121 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2099, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2134 q = 1) (hb : d94755 q = 1) : d98149 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2134, d98149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2134, d98149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2135 q = 1) (hb : d94755 q = 1) : d98150 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2135, d98150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2135, d98150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2136 q = 1) (hb : d94755 q = 1) : d98151 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2136, d98151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2136, d98151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro12657 (p : Pattern) (ha : d2139 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12639 q ha hb
    | true =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2137 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2138 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2139 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12658 (p : Pattern) (ha : d6550 p = 1) (hb : d94755 p = 1) : d98124 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2093 q = 1) (hb : d94755 q = 1) : d98119 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12638 q ha hb
    | true =>
      simp only [d2093, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2094 q = 1) (hb : d94755 q = 1) : d98120 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6547 q = 1) (hb : d94755 q = 1) : d98121 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6547, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6547, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6548 q = 1) (hb : d94755 q = 1) : d98122 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6548, d98122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6548, d98122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6549 q = 1) (hb : d94755 q = 1) : d98123 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6549, d98123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6549, d98123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6550 q = 1) (hb : d94755 q = 1) : d98124 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6550, d98124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6550, d98124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12659 (p : Pattern) (ha : d2070 p = 1) (hb : d94753 p = 1) : d13609 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2057 q = 1) : d2057 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2069 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2070 q = 1) (hb : d94753 q = 1) : d13609 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d2070, d94753, d13609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2070, d94753, d13609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro12660 (p : Pattern) (ha : d2155 p = 1) (hb : d94755 p = 1) : d98157 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2152 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2073 q = 1) (hb : d94753 q = 1) : d13610 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2073, d13610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12659 q ha hb
    | true =>
      simp only [d2073, d13610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12636 q ha hb
  have h3 (q : Pattern) (ha : d2074 q = 1) (hb : d94753 q = 1) : d13611 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2074, d13611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2074, d13611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2075 q = 1) (hb : d94753 q = 1) : d13612 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2075, d13612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2075, d13612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2153 q = 1) (hb : d94755 q = 1) : d98155 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2153, d94755, d98155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2153, d94755, d98155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d2075 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2086 q = 1) (hb : d94753 q = 1) : d13615 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2086, d13615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12636 q ha hb
    | true =>
      simp only [d2086, d13615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12637 q ha hb
  have h8 (q : Pattern) (ha : d2087 q = 1) (hb : d94753 q = 1) : d13616 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2087, d13616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2087, d13616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2088 q = 1) (hb : d94753 q = 1) : d13617 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2088, d13617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2088, d13617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2089 q = 1) (hb : d94755 q = 1) : d98116 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2089, d94755, d98116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d2089, d94755, d98116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2154 q = 1) (hb : d94755 q = 1) : d98156 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2154, d98156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2154, d98156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d2155 q = 1) (hb : d94755 q = 1) : d98157 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2155, d98157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2155, d98157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro12661 (p : Pattern) (ha : d7117 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2075 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7115 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7115, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7115, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5255 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5256 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5256, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d5256, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d7116 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7117 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12662 (p : Pattern) (ha : d7123 p = 1) (hb : d94755 p = 1) : d98163 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2156 q = 1) (hb : d94755 q = 1) : d98158 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2156, d98158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12660 q ha hb
    | true =>
      simp only [d2156, d98158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2157 q = 1) (hb : d94755 q = 1) : d98159 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2157, d98159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2157, d98159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7118 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12661 q ha hb
    | true =>
      simp only [d7118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7119 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7120 q = 1) (hb : d94755 q = 1) : d98160 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7120, d98160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7120, d98160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7121 q = 1) (hb : d94755 q = 1) : d98161 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7121, d98161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7121, d98161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7122 q = 1) (hb : d94755 q = 1) : d98162 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7122, d98162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7122, d98162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7123 q = 1) (hb : d94755 q = 1) : d98163 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7123, d98163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7123, d98163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro12663 (p : Pattern) (ha : d82237 p = 1) (hb : d94755 p = 1) : d98170 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2130 q = 1) (hb : d94755 q = 1) : d98145 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2130, d98145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12654 q ha hb
    | true =>
      simp only [d2130, d98145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12655 q ha hb
  have h2 (q : Pattern) (ha : d2131 q = 1) (hb : d94755 q = 1) : d98146 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2131, d98146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2131, d98146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2132 q = 1) (hb : d94755 q = 1) : d98147 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, d98147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2132, d98147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2133 q = 1) (hb : d94755 q = 1) : d98148 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, d98148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2133, d98148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2140 q = 1) (hb : d94755 q = 1) : d98152 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2140, d98152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12656 q ha hb
    | true =>
      simp only [d2140, d98152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12657 q ha hb
  have h6 (q : Pattern) (ha : d2141 q = 1) (hb : d94755 q = 1) : d98153 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2141, d98153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2141, d98153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2142 q = 1) (hb : d94755 q = 1) : d98154 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, d98154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2142, d98154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7128 q = 1) (hb : d94755 q = 1) : d98164 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7128, d98164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12662 q ha hb
    | true =>
      simp only [d7128, d98164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12652 q ha hb
  have h9 (q : Pattern) (ha : d82233 q = 1) (hb : d94755 q = 1) : d98165 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82233, d98165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d82233, d98165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6592 q = 1) (hb : d94755 q = 1) : d98125 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6592, d98125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12658 q ha hb
    | true =>
      simp only [d6592, d98125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d6593 q = 1) (hb : d94755 q = 1) : d98166 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6593, d98166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6593, d98166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d82234 q = 1) (hb : d94755 q = 1) : d98167 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82234, d98167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82234, d98167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d82235 q = 1) (hb : d94755 q = 1) : d98168 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82235, d98168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82235, d98168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d82236 q = 1) (hb : d94755 q = 1) : d98169 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82236, d98169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82236, d98169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d82237 q = 1) (hb : d94755 q = 1) : d98170 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82237, d98170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82237, d98170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro12664 (p : Pattern) (ha : d2281 p = 1) (hb : d94755 p = 1) : d98171 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2093 q = 1) (hb : d94755 q = 1) : d98119 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12638 q ha hb
    | true =>
      simp only [d2093, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2094 q = 1) (hb : d94755 q = 1) : d98120 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12639 q ha hb
    | true =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2099 q = 1) (hb : d94755 q = 1) : d98121 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2099, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2100 q = 1) (hb : d94755 q = 1) : d98122 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2100, d98122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2100, d98122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2126 q = 1) (hb : d94755 q = 1) : d98143 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2126, d98143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2126, d98143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2281 q = 1) (hb : d94755 q = 1) : d98171 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2281, d98171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2281, d98171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro12665 (p : Pattern) (ha : d2282 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12639 q ha hb
    | true =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2104 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2128 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2282 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro12666 (p : Pattern) (ha : d2287 p = 1) (hb : d94755 p = 1) : d98176 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2093 q = 1) (hb : d94755 q = 1) : d98119 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12638 q ha hb
    | true =>
      simp only [d2093, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2094 q = 1) (hb : d94755 q = 1) : d98120 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12639 q ha hb
    | true =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2099 q = 1) (hb : d94755 q = 1) : d98121 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2099, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2134 q = 1) (hb : d94755 q = 1) : d98149 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2134, d98149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2134, d98149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2135 q = 1) (hb : d94755 q = 1) : d98150 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2135, d98150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2135, d98150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2287 q = 1) (hb : d94755 q = 1) : d98176 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2287, d98176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2287, d98176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro12667 (p : Pattern) (ha : d2288 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12639 q ha hb
    | true =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2137 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2138 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2288 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro12668 (p : Pattern) (ha : d6559 p = 1) (hb : d94755 p = 1) : d98133 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2093 q = 1) (hb : d94755 q = 1) : d98119 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12638 q ha hb
    | true =>
      simp only [d2093, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2094 q = 1) (hb : d94755 q = 1) : d98120 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6547 q = 1) (hb : d94755 q = 1) : d98121 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6547, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6547, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6548 q = 1) (hb : d94755 q = 1) : d98122 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6548, d98122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6548, d98122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6549 q = 1) (hb : d94755 q = 1) : d98123 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6549, d98123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6549, d98123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6559 q = 1) (hb : d94755 q = 1) : d98133 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6559, d98133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6559, d98133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro12669 (p : Pattern) (ha : d7134 p = 1) (hb : d94755 p = 1) : d98180 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2156 q = 1) (hb : d94755 q = 1) : d98158 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2156, d98158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12660 q ha hb
    | true =>
      simp only [d2156, d98158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2157 q = 1) (hb : d94755 q = 1) : d98159 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2157, d98159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2157, d98159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7118 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12661 q ha hb
    | true =>
      simp only [d7118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7119 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7120 q = 1) (hb : d94755 q = 1) : d98160 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7120, d98160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7120, d98160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7121 q = 1) (hb : d94755 q = 1) : d98161 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7121, d98161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7121, d98161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7122 q = 1) (hb : d94755 q = 1) : d98162 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7122, d98162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7122, d98162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7134 q = 1) (hb : d94755 q = 1) : d98180 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7134, d98180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7134, d98180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro12670 (p : Pattern) (ha : d7135 p = 1) (hb : d94755 p = 1) : d98133 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5259 q = 1) (hb : d94755 q = 1) : d98119 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5259, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12651 q ha hb
    | true =>
      simp only [d5259, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5260 q = 1) (hb : d94755 q = 1) : d98120 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5260, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5260, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12639 q ha hb
    | true =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7124 q = 1) (hb : d94755 q = 1) : d98121 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7124, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7124, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7125 q = 1) (hb : d94755 q = 1) : d98122 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7125, d98122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7125, d98122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7126 q = 1) (hb : d94755 q = 1) : d98123 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7126, d98123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7126, d98123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7135 q = 1) (hb : d94755 q = 1) : d98133 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7135, d98133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7135, d98133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro12671 (p : Pattern) (ha : d82242 p = 1) (hb : d94755 p = 1) : d98187 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2130 q = 1) (hb : d94755 q = 1) : d98145 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2130, d98145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12654 q ha hb
    | true =>
      simp only [d2130, d98145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12655 q ha hb
  have h2 (q : Pattern) (ha : d2131 q = 1) (hb : d94755 q = 1) : d98146 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2131, d98146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2131, d98146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2132 q = 1) (hb : d94755 q = 1) : d98147 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, d98147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2132, d98147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2133 q = 1) (hb : d94755 q = 1) : d98148 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, d98148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2133, d98148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2140 q = 1) (hb : d94755 q = 1) : d98152 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2140, d98152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12656 q ha hb
    | true =>
      simp only [d2140, d98152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12657 q ha hb
  have h6 (q : Pattern) (ha : d2141 q = 1) (hb : d94755 q = 1) : d98153 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2141, d98153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2141, d98153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2142 q = 1) (hb : d94755 q = 1) : d98154 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, d98154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2142, d98154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7128 q = 1) (hb : d94755 q = 1) : d98164 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7128, d98164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12662 q ha hb
    | true =>
      simp only [d7128, d98164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12652 q ha hb
  have h9 (q : Pattern) (ha : d82233 q = 1) (hb : d94755 q = 1) : d98165 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82233, d98165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d82233, d98165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6592 q = 1) (hb : d94755 q = 1) : d98125 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6592, d98125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12658 q ha hb
    | true =>
      simp only [d6592, d98125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d6593 q = 1) (hb : d94755 q = 1) : d98166 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6593, d98166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6593, d98166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d82234 q = 1) (hb : d94755 q = 1) : d98167 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82234, d98167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82234, d98167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d82235 q = 1) (hb : d94755 q = 1) : d98168 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82235, d98168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82235, d98168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d82236 q = 1) (hb : d94755 q = 1) : d98169 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82236, d98169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82236, d98169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d2283 q = 1) (hb : d94755 q = 1) : d98172 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2283, d98172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12664 q ha hb
    | true =>
      simp only [d2283, d98172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12665 q ha hb
  have h16 (q : Pattern) (ha : d2284 q = 1) (hb : d94755 q = 1) : d98173 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2284, d98173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2284, d98173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d2285 q = 1) (hb : d94755 q = 1) : d98174 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2285, d98174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d2285, d98174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d2286 q = 1) (hb : d94755 q = 1) : d98175 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2286, d98175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2286, d98175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d2289 q = 1) (hb : d94755 q = 1) : d98177 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2289, d98177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12666 q ha hb
    | true =>
      simp only [d2289, d98177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12667 q ha hb
  have h20 (q : Pattern) (ha : d2290 q = 1) (hb : d94755 q = 1) : d98178 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2290, d98178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2290, d98178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d2291 q = 1) (hb : d94755 q = 1) : d98179 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2291, d98179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d2291, d98179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d7136 q = 1) (hb : d94755 q = 1) : d98181 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7136, d98181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12669 q ha hb
    | true =>
      simp only [d7136, d98181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12670 q ha hb
  have h23 (q : Pattern) (ha : d82238 q = 1) (hb : d94755 q = 1) : d98182 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82238, d98182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d82238, d98182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d6613 q = 1) (hb : d94755 q = 1) : d98134 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6613, d98134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12668 q ha hb
    | true =>
      simp only [d6613, d98134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d6614 q = 1) (hb : d94755 q = 1) : d98183 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6614, d98183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d6614, d98183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d82239 q = 1) (hb : d94755 q = 1) : d98184 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82239, d98184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d82239, d98184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d82240 q = 1) (hb : d94755 q = 1) : d98185 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82240, d98185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d82240, d98185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d82241 q = 1) (hb : d94755 q = 1) : d98186 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82241, d98186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d82241, d98186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d82242 q = 1) (hb : d94755 q = 1) : d98187 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82242, d98187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d82242, d98187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro12672 (p : Pattern) (ha : d82249 p = 1) (hb : d94755 p = 1) : d98196 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7136 q = 1) (hb : d94755 q = 1) : d98181 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7136, d98181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12669 q ha hb
    | true =>
      simp only [d7136, d98181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12670 q ha hb
  have h2 (q : Pattern) (ha : d82238 q = 1) (hb : d94755 q = 1) : d98182 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82238, d98182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82238, d98182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6613 q = 1) (hb : d94755 q = 1) : d98134 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6613, d98134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12668 q ha hb
    | true =>
      simp only [d6613, d98134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6614 q = 1) (hb : d94755 q = 1) : d98183 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6614, d98183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6614, d98183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82239 q = 1) (hb : d94755 q = 1) : d98184 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82239, d98184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82239, d98184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82247 q = 1) (hb : d94755 q = 1) : d98194 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82247, d98194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82247, d98194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82248 q = 1) (hb : d94755 q = 1) : d98195 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82248, d98195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82248, d98195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82249 q = 1) (hb : d94755 q = 1) : d98196 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82249, d98196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82249, d98196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro12673 (p : Pattern) (ha : d2356 p = 1) (hb : d94753 p = 1) : d6642 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2350 q = 1) : d2350 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2355 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2356 q = 1) (hb : d94753 q = 1) : d6642 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d2356, d94753, d6642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2356, d94753, d6642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro12674 (p : Pattern) (ha : d2366 p = 1) (hb : d94753 p = 1) : d13843 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2355 q = 1) : d2355 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2365 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2366 q = 1) (hb : d94753 q = 1) : d13843 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d2366, d94753, d13843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2366, d94753, d13843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro12675 (p : Pattern) (ha : d2377 p = 1) (hb : d94755 p = 1) : d98213 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2359 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2367 q = 1) (hb : d94753 q = 1) : d13844 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2367, d13844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12673 q ha hb
    | true =>
      simp only [d2367, d13844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12674 q ha hb
  have h3 (q : Pattern) (ha : d2368 q = 1) (hb : d94753 q = 1) : d13845 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2368, d13845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2368, d13845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2369 q = 1) (hb : d94753 q = 1) : d13846 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2369, d13846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2369, d13846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2370 q = 1) (hb : d94755 q = 1) : d98203 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2370, d94755, d98203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2370, d94755, d98203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d2369 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2375 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2375, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d2375, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d2376 q = 1) (hb : d94755 q = 1) : d98212 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2376, d98212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2376, d98212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2377 q = 1) (hb : d94755 q = 1) : d98213 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2377, d98213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2377, d98213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro12676 (p : Pattern) (ha : d6671 p = 1) (hb : d94755 p = 1) : d98219 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2378 q = 1) (hb : d94755 q = 1) : d98214 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2378, d98214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12675 q ha hb
    | true =>
      simp only [d2378, d98214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2379 q = 1) (hb : d94755 q = 1) : d98215 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2379, d98215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2379, d98215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6668 q = 1) (hb : d94755 q = 1) : d98216 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6668, d98216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6668, d98216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6669 q = 1) (hb : d94755 q = 1) : d98217 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6669, d98217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6669, d98217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6670 q = 1) (hb : d94755 q = 1) : d98218 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6670, d98218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6670, d98218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6671 q = 1) (hb : d94755 q = 1) : d98219 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6671, d98219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6671, d98219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro12677 (p : Pattern) (ha : d2351 p = 1) (hb : d94753 p = 1) : d13809 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2344 q = 1) : d2344 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2350 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2351 q = 1) (hb : d94753 q = 1) : d13809 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d2351, d94753, d13809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2351, d94753, d13809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro12678 (p : Pattern) (ha : d2372 p = 1) (hb : d94755 p = 1) : d98205 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2354 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2357 q = 1) (hb : d94753 q = 1) : d13827 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2357, d13827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12677 q ha hb
    | true =>
      simp only [d2357, d13827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12673 q ha hb
  have h3 (q : Pattern) (ha : d2358 q = 1) (hb : d94753 q = 1) : d13828 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2358, d13828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2358, d13828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2359 q = 1) (hb : d94753 q = 1) : d13829 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2359, d13829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2359, d13829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2360 q = 1) (hb : d94755 q = 1) : d98202 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2360, d94755, d98202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2360, d94755, d98202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d2359 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2367 q = 1) (hb : d94753 q = 1) : d13844 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2367, d13844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12673 q ha hb
    | true =>
      simp only [d2367, d13844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12674 q ha hb
  have h8 (q : Pattern) (ha : d2368 q = 1) (hb : d94753 q = 1) : d13845 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2368, d13845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2368, d13845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2369 q = 1) (hb : d94753 q = 1) : d13846 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2369, d13846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2369, d13846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2370 q = 1) (hb : d94755 q = 1) : d98203 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2370, d94755, d98203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d2370, d94755, d98203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2371 q = 1) (hb : d94755 q = 1) : d98204 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2371, d98204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2371, d98204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d2372 q = 1) (hb : d94755 q = 1) : d98205 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2372, d98205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2372, d98205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro12679 (p : Pattern) (ha : d7163 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2359 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7161 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7161, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7161, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6651 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6652 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6652, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d6652, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d7162 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7163 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12680 (p : Pattern) (ha : d7169 p = 1) (hb : d94755 p = 1) : d98211 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2373 q = 1) (hb : d94755 q = 1) : d98206 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2373, d98206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12678 q ha hb
    | true =>
      simp only [d2373, d98206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2374 q = 1) (hb : d94755 q = 1) : d98207 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2374, d98207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2374, d98207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7164 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12679 q ha hb
    | true =>
      simp only [d7164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7165 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7166 q = 1) (hb : d94755 q = 1) : d98208 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7166, d98208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7166, d98208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7167 q = 1) (hb : d94755 q = 1) : d98209 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7167, d98209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7167, d98209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7168 q = 1) (hb : d94755 q = 1) : d98210 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7168, d98210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7168, d98210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7169 q = 1) (hb : d94755 q = 1) : d98211 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7169, d98211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7169, d98211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro12681 (p : Pattern) (ha : d6654 p = 1) (hb : d94755 p = 1) : d98213 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2359 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2367 q = 1) (hb : d94753 q = 1) : d13844 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2367, d13844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12673 q ha hb
    | true =>
      simp only [d2367, d13844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12674 q ha hb
  have h3 (q : Pattern) (ha : d2368 q = 1) (hb : d94753 q = 1) : d13845 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2368, d13845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2368, d13845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2369 q = 1) (hb : d94753 q = 1) : d13846 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2369, d13846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2369, d13846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2370 q = 1) (hb : d94755 q = 1) : d98203 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2370, d94755, d98203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2370, d94755, d98203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6651 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6652 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6652, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d6652, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d6653 q = 1) (hb : d94755 q = 1) : d98212 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6653, d98212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6653, d98212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d6654 q = 1) (hb : d94755 q = 1) : d98213 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6654, d98213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6654, d98213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro12682 (p : Pattern) (ha : d7173 p = 1) (hb : d94755 p = 1) : d98219 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6655 q = 1) (hb : d94755 q = 1) : d98214 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6655, d98214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12681 q ha hb
    | true =>
      simp only [d6655, d98214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6656 q = 1) (hb : d94755 q = 1) : d98215 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6656, d98215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6656, d98215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2386 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12648 q ha hb
    | true =>
      simp only [d2386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2387 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7170 q = 1) (hb : d94755 q = 1) : d98216 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7170, d98216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7170, d98216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7171 q = 1) (hb : d94755 q = 1) : d98217 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7171, d98217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7171, d98217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7172 q = 1) (hb : d94755 q = 1) : d98218 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7172, d98218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7172, d98218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7173 q = 1) (hb : d94755 q = 1) : d98219 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7173, d98219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7173, d98219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro12683 (p : Pattern) (ha : d82259 p = 1) (hb : d94755 p = 1) : d98227 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7174 q = 1) (hb : d94755 q = 1) : d98220 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7174, d98220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12680 q ha hb
    | true =>
      simp only [d7174, d98220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12682 q ha hb
  have h2 (q : Pattern) (ha : d82255 q = 1) (hb : d94755 q = 1) : d98221 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82255, d98221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82255, d98221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6672 q = 1) (hb : d94755 q = 1) : d98222 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6672, d98222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12676 q ha hb
    | true =>
      simp only [d6672, d98222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6673 q = 1) (hb : d94755 q = 1) : d98223 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6673, d98223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6673, d98223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82256 q = 1) (hb : d94755 q = 1) : d98224 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82256, d98224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82256, d98224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82257 q = 1) (hb : d94755 q = 1) : d98225 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82257, d98225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82257, d98225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82258 q = 1) (hb : d94755 q = 1) : d98226 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82258, d98226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82258, d98226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82259 q = 1) (hb : d94755 q = 1) : d98227 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82259, d98227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82259, d98227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro12684 (p : Pattern) (ha : d82265 p = 1) (hb : d94755 p = 1) : d98233 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2113 q = 1) (hb : d94755 q = 1) : d98131 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2113, d98131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2113, d98131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12642 q ha hb
  have h2 (q : Pattern) (ha : d2114 q = 1) (hb : d94755 q = 1) : d98132 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2114, d98132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2114, d98132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2123 q = 1) (hb : d94755 q = 1) : d98140 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d98140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12642 q ha hb
    | true =>
      simp only [d2123, d98140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12645 q ha hb
  have h4 (q : Pattern) (ha : d2124 q = 1) (hb : d94755 q = 1) : d98141 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d98141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2124, d98141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2125 q = 1) (hb : d94755 q = 1) : d98142 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2125, d98142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2125, d98142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82243 q = 1) (hb : d94755 q = 1) : d98188 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82243, d98188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12663 q ha hb
    | true =>
      simp only [d82243, d98188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12671 q ha hb
  have h7 (q : Pattern) (ha : d7149 q = 1) (hb : d94755 q = 1) : d98190 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7149, d98190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12653 q ha hb
    | true =>
      simp only [d7149, d98190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12646 q ha hb
  have h8 (q : Pattern) (ha : d82244 q = 1) (hb : d94755 q = 1) : d98191 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82244, d98191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82244, d98191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d82245 q = 1) (hb : d94755 q = 1) : d98192 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82245, d98192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d82245, d98192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d82246 q = 1) (hb : d94755 q = 1) : d98193 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82246, d98193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82246, d98193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d82250 q = 1) (hb : d94755 q = 1) : d98197 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82250, d98197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82250, d98197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12672 q ha hb
  have h12 (q : Pattern) (ha : d2326 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12647 q ha hb
  have h13 (q : Pattern) (ha : d82251 q = 1) (hb : d94755 q = 1) : d98198 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82251, d98198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82251, d98198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d82252 q = 1) (hb : d94755 q = 1) : d98199 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82252, d98199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82252, d98199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d82253 q = 1) (hb : d94755 q = 1) : d98200 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82253, d98200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d82253, d98200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d82254 q = 1) (hb : d94755 q = 1) : d98201 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82254, d98201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82254, d98201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d82260 q = 1) (hb : d94755 q = 1) : d98228 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82260, d98228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82260, d98228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12683 q ha hb
  have h18 (q : Pattern) (ha : d2459 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12650 q ha hb
  have h19 (q : Pattern) (ha : d82261 q = 1) (hb : d94755 q = 1) : d98229 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82261, d98229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d82261, d98229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d82262 q = 1) (hb : d94755 q = 1) : d98230 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82262, d98230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d82262, d98230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d82263 q = 1) (hb : d94755 q = 1) : d98231 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82263, d98231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d82263, d98231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d82264 q = 1) (hb : d94755 q = 1) : d98232 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82264, d98232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d82264, d98232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d82265 q = 1) (hb : d94755 q = 1) : d98233 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82265, d98233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d82265, d98233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro12685 (p : Pattern) (ha : d82271 p = 1) (hb : d94755 p = 1) : d98239 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82266 q = 1) (hb : d94755 q = 1) : d98234 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82266, d98234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82266, d98234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12684 q ha hb
  have h2 (q : Pattern) (ha : d82267 q = 1) (hb : d94755 q = 1) : d98235 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82267, d98235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82267, d98235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82268 q = 1) (hb : d94755 q = 1) : d98236 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82268, d98236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82268, d98236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82269 q = 1) (hb : d94755 q = 1) : d98237 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82269, d98237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82269, d98237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82270 q = 1) (hb : d94755 q = 1) : d98238 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82270, d98238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82270, d98238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82271 q = 1) (hb : d94755 q = 1) : d98239 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82271, d98239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82271, d98239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12686 (p : Pattern) (ha : d82277 p = 1) (hb : d94755 p = 1) : d98245 p = 1 := by
  have h0 (q : Pattern) (ha : d82106 q = 1) (hb : d94755 q = 1) : d97734 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82106, d97734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12441 q ha hb
    | true =>
      simp only [d82106, d97734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12487 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d82146 q = 1) (hb : d94755 q = 1) : d97859 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82146, d97859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82146, d97859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12535 q ha hb
  have h3 (q : Pattern) (ha : d82147 q = 1) (hb : d94755 q = 1) : d97860 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82147, d97860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82147, d97860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82187 q = 1) (hb : d94755 q = 1) : d97985 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82187, d97985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82187, d97985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12585 q ha hb
  have h5 (q : Pattern) (ha : d82188 q = 1) (hb : d94755 q = 1) : d97986 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82188, d97986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82188, d97986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82189 q = 1) (hb : d94755 q = 1) : d97987 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d82189, d97987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82189, d97987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82229 q = 1) (hb : d94755 q = 1) : d98112 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82229, d98112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82229, d98112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12635 q ha hb
  have h8 (q : Pattern) (ha : d82230 q = 1) (hb : d94755 q = 1) : d98113 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82230, d98113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82230, d98113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d82231 q = 1) (hb : d94755 q = 1) : d98114 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d82231, d98114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82231, d98114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d82232 q = 1) (hb : d94755 q = 1) : d98115 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d82232, d98115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82232, d98115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d82272 q = 1) (hb : d94755 q = 1) : d98240 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82272, d98240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82272, d98240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12685 q ha hb
  have h12 (q : Pattern) (ha : d82273 q = 1) (hb : d94755 q = 1) : d98241 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82273, d98241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82273, d98241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d82274 q = 1) (hb : d94755 q = 1) : d98242 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d82274, d98242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82274, d98242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d82275 q = 1) (hb : d94755 q = 1) : d98243 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d82275, d98243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82275, d98243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d82276 q = 1) (hb : d94755 q = 1) : d98244 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d82276, d98244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82276, d98244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d82277 q = 1) (hb : d94755 q = 1) : d98245 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d82277, d98245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82277, d98245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro12687 (p : Pattern) (ha : d82283 p = 1) (hb : d94755 p = 1) : d98251 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82278 q = 1) (hb : d94755 q = 1) : d98246 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d82278, d98246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12686 q ha hb
    | true =>
      simp only [d82278, d98246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82279 q = 1) (hb : d94755 q = 1) : d98247 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d82279, d98247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82279, d98247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82280 q = 1) (hb : d94755 q = 1) : d98248 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d82280, d98248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82280, d98248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82281 q = 1) (hb : d94755 q = 1) : d98249 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d82281, d98249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82281, d98249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82282 q = 1) (hb : d94755 q = 1) : d98250 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d82282, d98250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82282, d98250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82283 q = 1) (hb : d94755 q = 1) : d98251 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d82283, d98251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82283, d98251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro12688 (p : Pattern) (ha : d82289 p = 1) (hb : d94755 p = 1) : d98257 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82284 q = 1) (hb : d94755 q = 1) : d98252 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d82284, d98252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12687 q ha hb
    | true =>
      simp only [d82284, d98252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82285 q = 1) (hb : d94755 q = 1) : d98253 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d82285, d98253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82285, d98253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82286 q = 1) (hb : d94755 q = 1) : d98254 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d82286, d98254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82286, d98254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82287 q = 1) (hb : d94755 q = 1) : d98255 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d82287, d98255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82287, d98255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82288 q = 1) (hb : d94755 q = 1) : d98256 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d82288, d98256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82288, d98256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82289 q = 1) (hb : d94755 q = 1) : d98257 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d82289, d98257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82289, d98257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro12689 (p : Pattern) (ha : d82295 p = 1) (hb : d94755 p = 1) : d98263 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82290 q = 1) (hb : d94755 q = 1) : d98258 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d82290, d98258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12688 q ha hb
    | true =>
      simp only [d82290, d98258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82291 q = 1) (hb : d94755 q = 1) : d98259 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d82291, d98259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82291, d98259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82292 q = 1) (hb : d94755 q = 1) : d98260 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d82292, d98260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82292, d98260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82293 q = 1) (hb : d94755 q = 1) : d98261 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d82293, d98261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82293, d98261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82294 q = 1) (hb : d94755 q = 1) : d98262 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d82294, d98262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82294, d98262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82295 q = 1) (hb : d94755 q = 1) : d98263 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d82295, d98263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82295, d98263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro12690 (p : Pattern) (ha : d82301 p = 1) (hb : d94755 p = 1) : d98269 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82296 q = 1) (hb : d94755 q = 1) : d98264 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d82296, d98264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12689 q ha hb
    | true =>
      simp only [d82296, d98264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82297 q = 1) (hb : d94755 q = 1) : d98265 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d82297, d98265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82297, d98265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82298 q = 1) (hb : d94755 q = 1) : d98266 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d82298, d98266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82298, d98266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82299 q = 1) (hb : d94755 q = 1) : d98267 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d82299, d98267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82299, d98267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82300 q = 1) (hb : d94755 q = 1) : d98268 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d82300, d98268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82300, d98268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82301 q = 1) (hb : d94755 q = 1) : d98269 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d82301, d98269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82301, d98269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro12691 (p : Pattern) (ha : d82307 p = 1) (hb : d94756 p = 1) : d98275 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82302 q = 1) (hb : d94755 q = 1) : d98270 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d82302, d98270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12690 q ha hb
    | true =>
      simp only [d82302, d98270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82303 q = 1) (hb : d94755 q = 1) : d98271 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d82303, d98271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82303, d98271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d82304 q = 1) (hb : d94756 q = 1) : d98272 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d82304, d94756, d98272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82304, d94756, d98272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d94756 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d82305 q = 1) (hb : d94756 q = 1) : d98273 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d82305, d98273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82305, d98273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82306 q = 1) (hb : d94756 q = 1) : d98274 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d82306, d98274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82306, d98274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d82307 q = 1) (hb : d94756 q = 1) : d98275 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d82307, d98275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82307, d98275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro12692 (p : Pattern) (ha : d82313 p = 1) (hb : d94756 p = 1) : d98281 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94756 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82308 q = 1) (hb : d94756 q = 1) : d98276 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d82308, d98276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12691 q ha hb
    | true =>
      simp only [d82308, d98276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82309 q = 1) (hb : d94756 q = 1) : d98277 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d82309, d98277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82309, d98277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82310 q = 1) (hb : d94756 q = 1) : d98278 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d82310, d98278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82310, d98278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82311 q = 1) (hb : d94756 q = 1) : d98279 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d82311, d98279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82311, d98279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82312 q = 1) (hb : d94756 q = 1) : d98280 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d82312, d98280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82312, d98280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82313 q = 1) (hb : d94756 q = 1) : d98281 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d82313, d98281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82313, d98281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro12693 (p : Pattern) (ha : d82319 p = 1) (hb : d94756 p = 1) : d98287 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94756 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82314 q = 1) (hb : d94756 q = 1) : d98282 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d82314, d98282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12692 q ha hb
    | true =>
      simp only [d82314, d98282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82315 q = 1) (hb : d94756 q = 1) : d98283 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d82315, d98283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82315, d98283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82316 q = 1) (hb : d94756 q = 1) : d98284 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d82316, d98284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82316, d98284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82317 q = 1) (hb : d94756 q = 1) : d98285 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d82317, d98285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82317, d98285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82318 q = 1) (hb : d94756 q = 1) : d98286 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d82318, d98286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82318, d98286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82319 q = 1) (hb : d94756 q = 1) : d98287 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d82319, d98287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82319, d98287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro12694 (p : Pattern) (ha : d30 p = 1) (hb : d51881 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27 q = 1) (hb : d51879 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28 q = 1) (hb : d51880 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29 q = 1) (hb : d51881 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, d51881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29, d51881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51881 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d30 q = 1) (hb : d51881 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12695 (p : Pattern) (ha : d96224 p = 1) (hb : d97457 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d96222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d31 q = 1) (hb : d96220 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d96220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12694 q ha hb
    | true =>
      simp only [d31, d96220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32 q = 1) (hb : d96221 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d96221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32, d96221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33 q = 1) (hb : d96222 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d96222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33, d96222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96222 q = 1) (hb : d97455 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d97455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d96223 q = 1) (hb : d97456 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96223, d97456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96223, d97456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d96224 q = 1) (hb : d97457 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96224, d97457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96224, d97457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro12696 (p : Pattern) (ha : d96230 p = 1) (hb : d97463 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96225 q = 1) (hb : d97458 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96225, d97458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12695 q ha hb
    | true =>
      simp only [d96225, d97458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96226 q = 1) (hb : d97459 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96226, d97459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96226, d97459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96227 q = 1) (hb : d97460 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96227, d97460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96227, d97460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96228 q = 1) (hb : d97461 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96228, d97461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96228, d97461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96229 q = 1) (hb : d97462 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96229, d97462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96229, d97462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96230 q = 1) (hb : d97463 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96230, d97463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96230, d97463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12697 (p : Pattern) (ha : d96236 p = 1) (hb : d97469 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96231 q = 1) (hb : d97464 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96231, d97464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12696 q ha hb
    | true =>
      simp only [d96231, d97464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96232 q = 1) (hb : d97465 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96232, d97465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d96232, d97465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d96233 q = 1) (hb : d97466 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96233, d97466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96233, d97466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96234 q = 1) (hb : d97467 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96234, d97467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96234, d97467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96235 q = 1) (hb : d97468 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96235, d97468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96235, d97468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96236 q = 1) (hb : d97469 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96236, d97469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96236, d97469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12698 (p : Pattern) (ha : d96237 p = 1) (hb : d97470 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96225 q = 1) (hb : d97458 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96225, d97458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12695 q ha hb
    | true =>
      simp only [d96225, d97458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96226 q = 1) (hb : d97459 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96226, d97459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96226, d97459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96227 q = 1) (hb : d97460 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96227, d97460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96227, d97460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96228 q = 1) (hb : d97461 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96228, d97461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96228, d97461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96229 q = 1) (hb : d97462 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96229, d97462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96229, d97462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96237 q = 1) (hb : d97470 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96237, d97470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96237, d97470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro12699 (p : Pattern) (ha : d96243 p = 1) (hb : d97476 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96231 q = 1) (hb : d97464 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96231, d97464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12696 q ha hb
    | true =>
      simp only [d96231, d97464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96232 q = 1) (hb : d97465 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96232, d97465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d96232, d97465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d96233 q = 1) (hb : d97466 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96233, d97466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96233, d97466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96234 q = 1) (hb : d97467 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96234, d97467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96234, d97467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96235 q = 1) (hb : d97468 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96235, d97468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96235, d97468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96238 q = 1) (hb : d97471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96238, d97471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12698 q ha hb
    | true =>
      simp only [d96238, d97471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96239 q = 1) (hb : d97472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96239, d97472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96239, d97472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d96240 q = 1) (hb : d97473 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96240, d97473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d96240, d97473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d96241 q = 1) (hb : d97474 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96241, d97474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96241, d97474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d96242 q = 1) (hb : d97475 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96242, d97475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96242, d97475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d96243 q = 1) (hb : d97476 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96243, d97476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96243, d97476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro12700 (p : Pattern) (ha : d96248 p = 1) (hb : d97481 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96238 q = 1) (hb : d97471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96238, d97471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12698 q ha hb
    | true =>
      simp only [d96238, d97471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96239 q = 1) (hb : d97472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96239, d97472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d96239, d97472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d96240 q = 1) (hb : d97473 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96240, d97473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96240, d97473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96241 q = 1) (hb : d97474 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96241, d97474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96241, d97474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96242 q = 1) (hb : d97475 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96242, d97475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96242, d97475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96248 q = 1) (hb : d97481 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96248, d97481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96248, d97481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12701 (p : Pattern) (ha : d71 p = 1) (hb : d51922 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d66 q = 1) (hb : d51918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
  have h2 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d67 q = 1) (hb : d51919 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d68 q = 1) (hb : d51920 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d70 q = 1) (hb : d51922 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, d51922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70, d51922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d51922 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d71 q = 1) (hb : d51922 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d71, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d71, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro12702 (p : Pattern) (ha : d96258 p = 1) (hb : d97489 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d96256 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d72 q = 1) (hb : d96254 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d96254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12701 q ha hb
    | true =>
      simp only [d72, d96254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d73 q = 1) (hb : d96255 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d96255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d73, d96255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74 q = 1) (hb : d96256 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d96256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74, d96256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96256 q = 1) (hb : d97487 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d97487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d96257 q = 1) (hb : d97488 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96257, d97488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96257, d97488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d96258 q = 1) (hb : d97489 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96258, d97489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96258, d97489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro12703 (p : Pattern) (ha : d96264 p = 1) (hb : d97495 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96259 q = 1) (hb : d97490 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96259, d97490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12702 q ha hb
    | true =>
      simp only [d96259, d97490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96260 q = 1) (hb : d97491 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96260, d97491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96260, d97491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96261 q = 1) (hb : d97492 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96261, d97492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96261, d97492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96262 q = 1) (hb : d97493 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96262, d97493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96262, d97493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96263 q = 1) (hb : d97494 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96263, d97494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96263, d97494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96264 q = 1) (hb : d97495 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96264, d97495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96264, d97495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro12704 (p : Pattern) (ha : d96270 p = 1) (hb : d97501 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96265 q = 1) (hb : d97496 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96265, d97496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12703 q ha hb
    | true =>
      simp only [d96265, d97496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96266 q = 1) (hb : d97497 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96266, d97497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d96266, d97497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d96267 q = 1) (hb : d97498 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96267, d97498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96267, d97498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96268 q = 1) (hb : d97499 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96268, d97499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96268, d97499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96269 q = 1) (hb : d97500 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96269, d97500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96269, d97500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96270 q = 1) (hb : d97501 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96270, d97501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96270, d97501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12705 (p : Pattern) (ha : d96276 p = 1) (hb : d97507 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96244 q = 1) (hb : d97477 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96244, d97477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12697 q ha hb
    | true =>
      simp only [d96244, d97477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12699 q ha hb
  have h2 (q : Pattern) (ha : d96245 q = 1) (hb : d97478 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96245, d97478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d96245, d97478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d96246 q = 1) (hb : d97479 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96246, d97479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96246, d97479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96247 q = 1) (hb : d97480 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96247, d97480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96247, d97480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96249 q = 1) (hb : d97482 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96249, d97482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96249, d97482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12700 q ha hb
  have h6 (q : Pattern) (ha : d96250 q = 1) (hb : d97483 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96250, d97483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96250, d97483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96251 q = 1) (hb : d97484 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96251, d97484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96251, d97484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d96252 q = 1) (hb : d97485 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96252, d97485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d96252, d97485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d96253 q = 1) (hb : d97486 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d96253, d97486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96253, d97486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d96271 q = 1) (hb : d97502 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96271, d97502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96271, d97502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12704 q ha hb
  have h11 (q : Pattern) (ha : d96272 q = 1) (hb : d97503 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96272, d97503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d96272, d97503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d96273 q = 1) (hb : d97504 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96273, d97504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d96273, d97504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d96274 q = 1) (hb : d97505 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96274, d97505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d96274, d97505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d96275 q = 1) (hb : d97506 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d96275, d97506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d96275, d97506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d96276 q = 1) (hb : d97507 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d96276, d97507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d96276, d97507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro12706 (p : Pattern) (ha : d96286 p = 1) (hb : d97517 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96231 q = 1) (hb : d97464 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96231, d97464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12696 q ha hb
    | true =>
      simp only [d96231, d97464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96282 q = 1) (hb : d97513 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96282, d97513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96282, d97513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96283 q = 1) (hb : d97514 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96283, d97514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96283, d97514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96284 q = 1) (hb : d97515 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96284, d97515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96284, d97515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96285 q = 1) (hb : d97516 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96285, d97516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96285, d97516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96286 q = 1) (hb : d97517 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96286, d97517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96286, d97517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12707 (p : Pattern) (ha : d96293 p = 1) (hb : d97524 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96231 q = 1) (hb : d97464 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96231, d97464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12696 q ha hb
    | true =>
      simp only [d96231, d97464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96282 q = 1) (hb : d97513 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96282, d97513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96282, d97513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96283 q = 1) (hb : d97514 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96283, d97514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96283, d97514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96284 q = 1) (hb : d97515 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96284, d97515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96284, d97515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96285 q = 1) (hb : d97516 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96285, d97516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96285, d97516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96238 q = 1) (hb : d97471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96238, d97471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12698 q ha hb
    | true =>
      simp only [d96238, d97471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96289 q = 1) (hb : d97520 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96289, d97520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96289, d97520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d96290 q = 1) (hb : d97521 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96290, d97521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d96290, d97521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d96291 q = 1) (hb : d97522 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96291, d97522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96291, d97522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d96292 q = 1) (hb : d97523 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96292, d97523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96292, d97523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d96293 q = 1) (hb : d97524 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96293, d97524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96293, d97524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro12708 (p : Pattern) (ha : d96298 p = 1) (hb : d97529 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96225 q = 1) (hb : d97458 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96225, d97458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12695 q ha hb
    | true =>
      simp only [d96225, d97458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96226 q = 1) (hb : d97459 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96226, d97459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96226, d97459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96227 q = 1) (hb : d97460 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96227, d97460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96227, d97460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96228 q = 1) (hb : d97461 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96228, d97461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96228, d97461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96297 q = 1) (hb : d97528 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96297, d97528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96297, d97528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96298 q = 1) (hb : d97529 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96298, d97529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96298, d97529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12709 (p : Pattern) (ha : d96305 p = 1) (hb : d97536 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96225 q = 1) (hb : d97458 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96225, d97458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12695 q ha hb
    | true =>
      simp only [d96225, d97458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96226 q = 1) (hb : d97459 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96226, d97459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96226, d97459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96227 q = 1) (hb : d97460 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96227, d97460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96227, d97460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96303 q = 1) (hb : d97534 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96303, d97534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96303, d97534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96304 q = 1) (hb : d97535 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96304, d97535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96304, d97535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96305 q = 1) (hb : d97536 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96305, d97536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96305, d97536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12710 (p : Pattern) (ha : d4818 p = 1) (hb : d51994 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d139 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
    | true =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d140 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d141 q = 1) (hb : d51992 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d51992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d51992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d142 q = 1) (hb : d51993 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d51993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d142, d51993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h9 (q : Pattern) (ha : d143 q = 1) (hb : d51994 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d143, d51994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d143, d51994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d51994 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d4818 q = 1) (hb : d51994 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d4818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro12711 (p : Pattern) (ha : d96313 p = 1) (hb : d97542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d96311 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4819 q = 1) (hb : d96309 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d96309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12710 q ha hb
    | true =>
      simp only [d4819, d96309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12694 q ha hb
  have h3 (q : Pattern) (ha : d4820 q = 1) (hb : d96310 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d96310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4820, d96310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4821 q = 1) (hb : d96311 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d96311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4821, d96311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96311 q = 1) (hb : d97540 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d97540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d96222 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d31 q = 1) (hb : d96220 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d96220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12694 q ha hb
    | true =>
      simp only [d31, d96220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d32 q = 1) (hb : d96221 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d96221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32, d96221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d96222 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d96222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33, d96222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d96222 q = 1) (hb : d97455 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d97455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d97455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d96312 q = 1) (hb : d97541 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96312, d97541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96312, d97541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d96313 q = 1) (hb : d97542 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96313, d97542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d96313, d97542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h12 p ha hb
theorem andIntro12712 (p : Pattern) (ha : d96319 p = 1) (hb : d97548 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96314 q = 1) (hb : d97543 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96314, d97543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12711 q ha hb
    | true =>
      simp only [d96314, d97543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96315 q = 1) (hb : d97544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96315, d97544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96315, d97544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96226 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96316 q = 1) (hb : d97545 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96316, d97545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96316, d97545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96317 q = 1) (hb : d97546 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96317, d97546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96317, d97546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96318 q = 1) (hb : d97547 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96318, d97547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96318, d97547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96319 q = 1) (hb : d97548 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96319, d97548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96319, d97548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12713 (p : Pattern) (ha : d96325 p = 1) (hb : d97554 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96299 q = 1) (hb : d97530 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96299, d97530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12708 q ha hb
    | true =>
      simp only [d96299, d97530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96300 q = 1) (hb : d97531 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96300, d97531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96300, d97531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96301 q = 1) (hb : d97532 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96301, d97532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96301, d97532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96302 q = 1) (hb : d97533 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96302, d97533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96302, d97533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96306 q = 1) (hb : d97537 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96306, d97537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12709 q ha hb
    | true =>
      simp only [d96306, d97537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96307 q = 1) (hb : d97538 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96307, d97538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96307, d97538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d96308 q = 1) (hb : d97539 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96308, d97539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96308, d97539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d96320 q = 1) (hb : d97549 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96320, d97549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12712 q ha hb
    | true =>
      simp only [d96320, d97549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12696 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d96231 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d96321 q = 1) (hb : d97550 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96321, d97550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d96321, d97550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d96231 q = 1) (hb : d97464 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96231, d97464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12696 q ha hb
    | true =>
      simp only [d96231, d97464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d96232 q = 1) (hb : d97465 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96232, d97465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d96232, d97465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d96322 q = 1) (hb : d97551 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96322, d97551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d96322, d97551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d96323 q = 1) (hb : d97552 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96323, d97552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d96323, d97552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d96324 q = 1) (hb : d97553 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96324, d97553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96324, d97553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d96325 q = 1) (hb : d97554 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96325, d97554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96325, d97554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro12714 (p : Pattern) (ha : d96326 p = 1) (hb : d97555 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96225 q = 1) (hb : d97458 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96225, d97458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12695 q ha hb
    | true =>
      simp only [d96225, d97458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96226 q = 1) (hb : d97459 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96226, d97459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96226, d97459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96227 q = 1) (hb : d97460 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96227, d97460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96227, d97460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96228 q = 1) (hb : d97461 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96228, d97461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96228, d97461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96297 q = 1) (hb : d97528 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96297, d97528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96297, d97528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96326 q = 1) (hb : d97555 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96326, d97555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96326, d97555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro12715 (p : Pattern) (ha : d96331 p = 1) (hb : d97560 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96225 q = 1) (hb : d97458 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96225, d97458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12695 q ha hb
    | true =>
      simp only [d96225, d97458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96226 q = 1) (hb : d97459 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96226, d97459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96226, d97459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96227 q = 1) (hb : d97460 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96227, d97460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96227, d97460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96303 q = 1) (hb : d97534 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96303, d97534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96303, d97534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96304 q = 1) (hb : d97535 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96304, d97535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96304, d97535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96331 q = 1) (hb : d97560 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96331, d97560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96331, d97560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro12716 (p : Pattern) (ha : d96335 p = 1) (hb : d97564 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96314 q = 1) (hb : d97543 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96314, d97543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12711 q ha hb
    | true =>
      simp only [d96314, d97543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96315 q = 1) (hb : d97544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96315, d97544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96315, d97544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96226 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96316 q = 1) (hb : d97545 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96316, d97545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96316, d97545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96317 q = 1) (hb : d97546 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96317, d97546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96317, d97546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96318 q = 1) (hb : d97547 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96318, d97547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96318, d97547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96335 q = 1) (hb : d97564 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96335, d97564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96335, d97564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12717 (p : Pattern) (ha : d96341 p = 1) (hb : d97570 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96299 q = 1) (hb : d97530 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96299, d97530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12708 q ha hb
    | true =>
      simp only [d96299, d97530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96300 q = 1) (hb : d97531 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96300, d97531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96300, d97531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96301 q = 1) (hb : d97532 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96301, d97532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96301, d97532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96302 q = 1) (hb : d97533 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96302, d97533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96302, d97533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96306 q = 1) (hb : d97537 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96306, d97537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12709 q ha hb
    | true =>
      simp only [d96306, d97537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96307 q = 1) (hb : d97538 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96307, d97538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96307, d97538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d96308 q = 1) (hb : d97539 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96308, d97539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96308, d97539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d96320 q = 1) (hb : d97549 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96320, d97549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12712 q ha hb
    | true =>
      simp only [d96320, d97549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12696 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d96231 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d96321 q = 1) (hb : d97550 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96321, d97550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d96321, d97550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d96231 q = 1) (hb : d97464 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96231, d97464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12696 q ha hb
    | true =>
      simp only [d96231, d97464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d96232 q = 1) (hb : d97465 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96232, d97465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d96232, d97465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d96322 q = 1) (hb : d97551 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96322, d97551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d96322, d97551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d96323 q = 1) (hb : d97552 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96323, d97552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d96323, d97552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d96324 q = 1) (hb : d97553 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96324, d97553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96324, d97553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d96327 q = 1) (hb : d97556 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96327, d97556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12714 q ha hb
    | true =>
      simp only [d96327, d97556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d96328 q = 1) (hb : d97557 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96328, d97557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96328, d97557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d96329 q = 1) (hb : d97558 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96329, d97558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d96329, d97558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d96330 q = 1) (hb : d97559 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96330, d97559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96330, d97559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d96332 q = 1) (hb : d97561 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96332, d97561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12715 q ha hb
    | true =>
      simp only [d96332, d97561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d96333 q = 1) (hb : d97562 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96333, d97562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96333, d97562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d96334 q = 1) (hb : d97563 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96334, d97563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d96334, d97563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d96336 q = 1) (hb : d97565 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96336, d97565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12716 q ha hb
    | true =>
      simp only [d96336, d97565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12698 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d96238 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d96337 q = 1) (hb : d97566 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96337, d97566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d96337, d97566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d96238 q = 1) (hb : d97471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96238, d97471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12698 q ha hb
    | true =>
      simp only [d96238, d97471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d96239 q = 1) (hb : d97472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96239, d97472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d96239, d97472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d96338 q = 1) (hb : d97567 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96338, d97567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d96338, d97567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d96339 q = 1) (hb : d97568 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96339, d97568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d96339, d97568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d96340 q = 1) (hb : d97569 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96340, d97569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d96340, d97569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d96341 q = 1) (hb : d97570 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96341, d97570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d96341, d97570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro12718 (p : Pattern) (ha : d96343 p = 1) (hb : d97572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96231 q = 1) (hb : d97464 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96231, d97464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12696 q ha hb
    | true =>
      simp only [d96231, d97464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96282 q = 1) (hb : d97513 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96282, d97513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96282, d97513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96283 q = 1) (hb : d97514 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96283, d97514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96283, d97514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96284 q = 1) (hb : d97515 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96284, d97515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96284, d97515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96285 q = 1) (hb : d97516 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96285, d97516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96285, d97516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96343 q = 1) (hb : d97572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96343, d97572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96343, d97572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro12719 (p : Pattern) (ha : d96350 p = 1) (hb : d97579 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96336 q = 1) (hb : d97565 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96336, d97565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12716 q ha hb
    | true =>
      simp only [d96336, d97565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12698 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d96238 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d96337 q = 1) (hb : d97566 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96337, d97566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d96337, d97566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d96238 q = 1) (hb : d97471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96238, d97471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12698 q ha hb
    | true =>
      simp only [d96238, d97471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96239 q = 1) (hb : d97472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96239, d97472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96239, d97472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96338 q = 1) (hb : d97567 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96338, d97567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96338, d97567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d96348 q = 1) (hb : d97577 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96348, d97577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96348, d97577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d96349 q = 1) (hb : d97578 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96349, d97578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96349, d97578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d96350 q = 1) (hb : d97579 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96350, d97579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96350, d97579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro12720 (p : Pattern) (ha : d6078 p = 1) (hb : d52048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d226 q = 1) (hb : d52044 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
  have h2 (q : Pattern) (ha : d139 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
    | true =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d227 q = 1) (hb : d52045 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d227, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d140 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d228 q = 1) (hb : d52046 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d228, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d229 q = 1) (hb : d52047 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d229, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h13 (q : Pattern) (ha : d230 q = 1) (hb : d52048 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d230, d52048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d230, d52048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52048 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d6078 q = 1) (hb : d52048 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d6078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro12721 (p : Pattern) (ha : d96360 p = 1) (hb : d97587 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d96358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6079 q = 1) (hb : d96356 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d96356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12720 q ha hb
    | true =>
      simp only [d6079, d96356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12701 q ha hb
  have h3 (q : Pattern) (ha : d6080 q = 1) (hb : d96357 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d96357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6080, d96357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6081 q = 1) (hb : d96358 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d96358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6081, d96358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96358 q = 1) (hb : d97585 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d97585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d96256 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d72 q = 1) (hb : d96254 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d96254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12701 q ha hb
    | true =>
      simp only [d72, d96254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d73 q = 1) (hb : d96255 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d96255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d73, d96255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74 q = 1) (hb : d96256 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d96256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74, d96256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d96256 q = 1) (hb : d97487 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d97487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d97487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d96359 q = 1) (hb : d97586 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96359, d97586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96359, d97586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d96360 q = 1) (hb : d97587 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96360, d97587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d96360, d97587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h12 p ha hb
theorem andIntro12722 (p : Pattern) (ha : d96366 p = 1) (hb : d97593 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96361 q = 1) (hb : d97588 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96361, d97588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12721 q ha hb
    | true =>
      simp only [d96361, d97588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96362 q = 1) (hb : d97589 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96362, d97589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96362, d97589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96260 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96363 q = 1) (hb : d97590 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96363, d97590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96363, d97590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96364 q = 1) (hb : d97591 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96364, d97591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96364, d97591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96365 q = 1) (hb : d97592 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96365, d97592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96365, d97592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96366 q = 1) (hb : d97593 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96366, d97593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96366, d97593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12723 (p : Pattern) (ha : d96372 p = 1) (hb : d97599 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96367 q = 1) (hb : d97594 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96367, d97594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12722 q ha hb
    | true =>
      simp only [d96367, d97594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12703 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d96265 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d96368 q = 1) (hb : d97595 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96368, d97595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d96368, d97595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d96265 q = 1) (hb : d97496 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96265, d97496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12703 q ha hb
    | true =>
      simp only [d96265, d97496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96266 q = 1) (hb : d97497 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96266, d97497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96266, d97497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96369 q = 1) (hb : d97596 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96369, d97596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96369, d97596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d96370 q = 1) (hb : d97597 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96370, d97597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96370, d97597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d96371 q = 1) (hb : d97598 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96371, d97598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96371, d97598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d96372 q = 1) (hb : d97599 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96372, d97599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96372, d97599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro12724 (p : Pattern) (ha : d96378 p = 1) (hb : d97605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96287 q = 1) (hb : d97518 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96287, d97518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96287, d97518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12706 q ha hb
  have h2 (q : Pattern) (ha : d96288 q = 1) (hb : d97519 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96288, d97519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d96288, d97519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d96294 q = 1) (hb : d97525 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96294, d97525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12706 q ha hb
    | true =>
      simp only [d96294, d97525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12707 q ha hb
  have h4 (q : Pattern) (ha : d96295 q = 1) (hb : d97526 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96295, d97526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96295, d97526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96296 q = 1) (hb : d97527 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96296, d97527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96296, d97527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96342 q = 1) (hb : d97571 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96342, d97571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12713 q ha hb
    | true =>
      simp only [d96342, d97571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12717 q ha hb
  have h7 (q : Pattern) (ha : d96344 q = 1) (hb : d97573 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96344, d97573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12718 q ha hb
    | true =>
      simp only [d96344, d97573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d96345 q = 1) (hb : d97574 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96345, d97574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96345, d97574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d96346 q = 1) (hb : d97575 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96346, d97575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d96346, d97575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d96347 q = 1) (hb : d97576 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96347, d97576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96347, d97576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d96351 q = 1) (hb : d97580 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96351, d97580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96351, d97580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12719 q ha hb
  have h12 (q : Pattern) (ha : d96352 q = 1) (hb : d97581 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96352, d97581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d96352, d97581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d96353 q = 1) (hb : d97582 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96353, d97582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d96353, d97582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d96354 q = 1) (hb : d97583 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96354, d97583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d96354, d97583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d96355 q = 1) (hb : d97584 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d96355, d97584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d96355, d97584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d96373 q = 1) (hb : d97600 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96373, d97600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96373, d97600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12723 q ha hb
  have h17 (q : Pattern) (ha : d96374 q = 1) (hb : d97601 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96374, d97601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d96374, d97601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d96375 q = 1) (hb : d97602 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96375, d97602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d96375, d97602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d96376 q = 1) (hb : d97603 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96376, d97603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d96376, d97603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d96377 q = 1) (hb : d97604 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d96377, d97604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d96377, d97604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d96378 q = 1) (hb : d97605 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d96378, d97605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d96378, d97605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro12725 (p : Pattern) (ha : d96384 p = 1) (hb : d97611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96277 q = 1) (hb : d97508 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96277, d97508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96277, d97508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12705 q ha hb
  have h2 (q : Pattern) (ha : d96278 q = 1) (hb : d97509 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d96278, d97509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96278, d97509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96279 q = 1) (hb : d97510 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d96279, d97510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96279, d97510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d96280 q = 1) (hb : d97511 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d96280, d97511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96280, d97511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96281 q = 1) (hb : d97512 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d96281, d97512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96281, d97512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96379 q = 1) (hb : d97606 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96379, d97606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96379, d97606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12724 q ha hb
  have h7 (q : Pattern) (ha : d96380 q = 1) (hb : d97607 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d96380, d97607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96380, d97607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d96381 q = 1) (hb : d97608 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d96381, d97608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96381, d97608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d96382 q = 1) (hb : d97609 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d96382, d97609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96382, d97609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d96383 q = 1) (hb : d97610 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d96383, d97610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96383, d97610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d96384 q = 1) (hb : d97611 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d96384, d97611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96384, d97611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro12726 (p : Pattern) (ha : d96313 p = 1) (hb : d97613 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d96311 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4819 q = 1) (hb : d96309 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d96309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12710 q ha hb
    | true =>
      simp only [d4819, d96309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12694 q ha hb
  have h3 (q : Pattern) (ha : d4820 q = 1) (hb : d96310 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d96310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4820, d96310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4821 q = 1) (hb : d96311 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d96311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4821, d96311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96311 q = 1) (hb : d97540 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d97540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d96222 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d96312 q = 1) (hb : d97612 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96312, d97612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96312, d97612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d96313 q = 1) (hb : d97613 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96313, d97613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d96313, d97613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro12727 (p : Pattern) (ha : d96319 p = 1) (hb : d97619 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96314 q = 1) (hb : d97614 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96314, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12726 q ha hb
    | true =>
      simp only [d96314, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96315 q = 1) (hb : d97615 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96315, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96315, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96226 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96316 q = 1) (hb : d97616 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96316, d97616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96316, d97616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96317 q = 1) (hb : d97617 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96317, d97617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96317, d97617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96318 q = 1) (hb : d97618 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96318, d97618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96318, d97618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96319 q = 1) (hb : d97619 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96319, d97619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96319, d97619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12728 (p : Pattern) (ha : d96389 p = 1) (hb : d97625 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d96230 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d96320 q = 1) (hb : d97620 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96320, d97620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12727 q ha hb
    | true =>
      simp only [d96320, d97620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d96385 q = 1) (hb : d97621 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96385, d97621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96385, d97621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d96386 q = 1) (hb : d97622 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96386, d97622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96386, d97622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96387 q = 1) (hb : d97623 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96387, d97623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96387, d97623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96388 q = 1) (hb : d97624 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96388, d97624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96388, d97624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d96389 q = 1) (hb : d97625 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96389, d97625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96389, d97625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12729 (p : Pattern) (ha : d96335 p = 1) (hb : d97628 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96314 q = 1) (hb : d97614 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96314, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12726 q ha hb
    | true =>
      simp only [d96314, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96315 q = 1) (hb : d97615 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96315, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96315, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96226 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96316 q = 1) (hb : d97616 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96316, d97616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96316, d97616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96317 q = 1) (hb : d97617 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96317, d97617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96317, d97617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96318 q = 1) (hb : d97618 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96318, d97618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96318, d97618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96335 q = 1) (hb : d97628 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96335, d97628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96335, d97628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12730 (p : Pattern) (ha : d96396 p = 1) (hb : d97634 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d96230 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d96320 q = 1) (hb : d97620 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96320, d97620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12727 q ha hb
    | true =>
      simp only [d96320, d97620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d96385 q = 1) (hb : d97621 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96385, d97621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96385, d97621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d96386 q = 1) (hb : d97622 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96386, d97622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96386, d97622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96387 q = 1) (hb : d97623 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96387, d97623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96387, d97623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96388 q = 1) (hb : d97624 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96388, d97624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96388, d97624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d96237 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d96336 q = 1) (hb : d97629 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96336, d97629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12729 q ha hb
    | true =>
      simp only [d96336, d97629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d96392 q = 1) (hb : d97630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96392, d97630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96392, d97630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d96393 q = 1) (hb : d97631 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96393, d97631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d96393, d97631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d96394 q = 1) (hb : d97632 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96394, d97632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96394, d97632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d96395 q = 1) (hb : d97633 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96395, d97633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96395, d97633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d96396 q = 1) (hb : d97634 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96396, d97634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96396, d97634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro12731 (p : Pattern) (ha : d96401 p = 1) (hb : d97639 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96314 q = 1) (hb : d97614 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96314, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12726 q ha hb
    | true =>
      simp only [d96314, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96315 q = 1) (hb : d97615 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96315, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96315, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96226 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96316 q = 1) (hb : d97616 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96316, d97616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96316, d97616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96317 q = 1) (hb : d97617 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96317, d97617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96317, d97617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96400 q = 1) (hb : d97638 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96400, d97638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96400, d97638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d96401 q = 1) (hb : d97639 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96401, d97639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96401, d97639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12732 (p : Pattern) (ha : d96408 p = 1) (hb : d97646 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96314 q = 1) (hb : d97614 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96314, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12726 q ha hb
    | true =>
      simp only [d96314, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96315 q = 1) (hb : d97615 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96315, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96315, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96226 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96316 q = 1) (hb : d97616 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96316, d97616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96316, d97616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96406 q = 1) (hb : d97644 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96406, d97644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96406, d97644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96407 q = 1) (hb : d97645 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96407, d97645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96407, d97645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96408 q = 1) (hb : d97646 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96408, d97646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96408, d97646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12733 (p : Pattern) (ha : d12312 p = 1) (hb : d52122 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d139 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
    | true =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d140 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d141 q = 1) (hb : d51992 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d51992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d51992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d142 q = 1) (hb : d51993 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d51993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d142, d51993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d323 q = 1) (hb : d52122 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d323, d52122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d323, d52122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52122 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d12312 q = 1) (hb : d52122 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro12734 (p : Pattern) (ha : d96416 p = 1) (hb : d97652 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d96414 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12313 q = 1) (hb : d96412 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12313, d96412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12733 q ha hb
    | true =>
      simp only [d12313, d96412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12710 q ha hb
  have h3 (q : Pattern) (ha : d12314 q = 1) (hb : d96413 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12314, d96413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12314, d96413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12315 q = 1) (hb : d96414 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12315, d96414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12315, d96414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96414 q = 1) (hb : d97650 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d97650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d96311 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4819 q = 1) (hb : d96309 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d96309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12710 q ha hb
    | true =>
      simp only [d4819, d96309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12694 q ha hb
  have h8 (q : Pattern) (ha : d4820 q = 1) (hb : d96310 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d96310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4820, d96310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4821 q = 1) (hb : d96311 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d96311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4821, d96311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d96311 q = 1) (hb : d97540 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d97540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d97540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d96415 q = 1) (hb : d97651 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96415, d97651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96415, d97651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d96416 q = 1) (hb : d97652 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96416, d97652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d96416, d97652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h12 p ha hb
theorem andIntro12735 (p : Pattern) (ha : d96426 p = 1) (hb : d97658 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96417 q = 1) (hb : d97653 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96417, d97653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12734 q ha hb
    | true =>
      simp only [d96417, d97653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96418 q = 1) (hb : d97654 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96418, d97654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96418, d97654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96422 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96423 q = 1) (hb : d97655 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96423, d97655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96423, d97655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96424 q = 1) (hb : d97656 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96424, d97656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96424, d97656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96425 q = 1) (hb : d97657 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96425, d97657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96425, d97657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96426 q = 1) (hb : d97658 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96426, d97658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96426, d97658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12736 (p : Pattern) (ha : d96420 p = 1) (hb : d97613 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d96311 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4819 q = 1) (hb : d96309 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d96309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12710 q ha hb
    | true =>
      simp only [d4819, d96309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12694 q ha hb
  have h3 (q : Pattern) (ha : d4820 q = 1) (hb : d96310 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d96310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4820, d96310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4821 q = 1) (hb : d96311 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d96311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4821, d96311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96311 q = 1) (hb : d97540 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d97540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d96419 q = 1) (hb : d97612 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96419, d97612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96419, d97612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d96420 q = 1) (hb : d97613 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96420, d97613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96420, d97613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro12737 (p : Pattern) (ha : d96430 p = 1) (hb : d97619 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96421 q = 1) (hb : d97614 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96421, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12736 q ha hb
    | true =>
      simp only [d96421, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96422 q = 1) (hb : d97615 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96422, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96422, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96226 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96427 q = 1) (hb : d97616 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96427, d97616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96427, d97616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96428 q = 1) (hb : d97617 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96428, d97617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96428, d97617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96429 q = 1) (hb : d97618 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96429, d97618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96429, d97618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96430 q = 1) (hb : d97619 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96430, d97619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96430, d97619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12738 (p : Pattern) (ha : d96436 p = 1) (hb : d97619 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96314 q = 1) (hb : d97614 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96314, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12726 q ha hb
    | true =>
      simp only [d96314, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96315 q = 1) (hb : d97615 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96315, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96315, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96433 q = 1) (hb : d97616 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96433, d97616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96433, d97616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96434 q = 1) (hb : d97617 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96434, d97617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96434, d97617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96435 q = 1) (hb : d97618 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96435, d97618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96435, d97618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96436 q = 1) (hb : d97619 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96436, d97619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96436, d97619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12739 (p : Pattern) (ha : d96442 p = 1) (hb : d97665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d96298 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d96402 q = 1) (hb : d97640 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96402, d97640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12731 q ha hb
    | true =>
      simp only [d96402, d97640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d96403 q = 1) (hb : d97641 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96403, d97641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96403, d97641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d96404 q = 1) (hb : d97642 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96404, d97642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96404, d97642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96405 q = 1) (hb : d97643 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96405, d97643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96405, d97643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d96305 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d96409 q = 1) (hb : d97647 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96409, d97647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12732 q ha hb
    | true =>
      simp only [d96409, d97647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d96410 q = 1) (hb : d97648 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96410, d97648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96410, d97648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d96411 q = 1) (hb : d97649 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96411, d97649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d96411, d97649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d96431 q = 1) (hb : d97659 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96431, d97659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12735 q ha hb
    | true =>
      simp only [d96431, d97659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12737 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d96320 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d96432 q = 1) (hb : d97660 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96432, d97660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d96432, d97660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d96437 q = 1) (hb : d97620 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96437, d97620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12738 q ha hb
    | true =>
      simp only [d96437, d97620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d96438 q = 1) (hb : d97661 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96438, d97661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d96438, d97661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d96439 q = 1) (hb : d97662 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96439, d97662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d96439, d97662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d96440 q = 1) (hb : d97663 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96440, d97663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d96440, d97663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d96441 q = 1) (hb : d97664 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96441, d97664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96441, d97664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d96442 q = 1) (hb : d97665 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96442, d97665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96442, d97665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro12740 (p : Pattern) (ha : d96443 p = 1) (hb : d97666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96314 q = 1) (hb : d97614 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96314, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12726 q ha hb
    | true =>
      simp only [d96314, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96315 q = 1) (hb : d97615 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96315, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96315, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96226 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96316 q = 1) (hb : d97616 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96316, d97616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96316, d97616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96317 q = 1) (hb : d97617 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96317, d97617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96317, d97617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96400 q = 1) (hb : d97638 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96400, d97638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96400, d97638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d96443 q = 1) (hb : d97666 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96443, d97666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96443, d97666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12741 (p : Pattern) (ha : d96448 p = 1) (hb : d97671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96314 q = 1) (hb : d97614 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96314, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12726 q ha hb
    | true =>
      simp only [d96314, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96315 q = 1) (hb : d97615 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96315, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96315, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96226 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96316 q = 1) (hb : d97616 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96316, d97616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96316, d97616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96406 q = 1) (hb : d97644 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96406, d97644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96406, d97644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96407 q = 1) (hb : d97645 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96407, d97645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96407, d97645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96448 q = 1) (hb : d97671 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96448, d97671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96448, d97671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12742 (p : Pattern) (ha : d96452 p = 1) (hb : d97675 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96417 q = 1) (hb : d97653 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96417, d97653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12734 q ha hb
    | true =>
      simp only [d96417, d97653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96418 q = 1) (hb : d97654 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96418, d97654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96418, d97654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96422 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96423 q = 1) (hb : d97655 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96423, d97655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96423, d97655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96424 q = 1) (hb : d97656 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96424, d97656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96424, d97656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96425 q = 1) (hb : d97657 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96425, d97657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96425, d97657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96452 q = 1) (hb : d97675 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96452, d97675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96452, d97675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12743 (p : Pattern) (ha : d96453 p = 1) (hb : d97628 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96421 q = 1) (hb : d97614 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96421, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12736 q ha hb
    | true =>
      simp only [d96421, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96422 q = 1) (hb : d97615 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96422, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96422, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96226 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96427 q = 1) (hb : d97616 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96427, d97616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96427, d97616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96428 q = 1) (hb : d97617 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96428, d97617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96428, d97617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96429 q = 1) (hb : d97618 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96429, d97618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96429, d97618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96453 q = 1) (hb : d97628 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96453, d97628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96453, d97628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12744 (p : Pattern) (ha : d96456 p = 1) (hb : d97628 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96314 q = 1) (hb : d97614 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96314, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12726 q ha hb
    | true =>
      simp only [d96314, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96315 q = 1) (hb : d97615 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96315, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96315, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96433 q = 1) (hb : d97616 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96433, d97616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96433, d97616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96434 q = 1) (hb : d97617 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96434, d97617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96434, d97617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96435 q = 1) (hb : d97618 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96435, d97618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96435, d97618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96456 q = 1) (hb : d97628 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96456, d97628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96456, d97628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro12745 (p : Pattern) (ha : d96462 p = 1) (hb : d97682 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d96298 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d96402 q = 1) (hb : d97640 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96402, d97640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12731 q ha hb
    | true =>
      simp only [d96402, d97640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d96403 q = 1) (hb : d97641 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96403, d97641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96403, d97641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d96404 q = 1) (hb : d97642 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96404, d97642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96404, d97642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96405 q = 1) (hb : d97643 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96405, d97643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96405, d97643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d96305 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d96409 q = 1) (hb : d97647 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96409, d97647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12732 q ha hb
    | true =>
      simp only [d96409, d97647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d96410 q = 1) (hb : d97648 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96410, d97648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96410, d97648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d96411 q = 1) (hb : d97649 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96411, d97649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d96411, d97649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d96431 q = 1) (hb : d97659 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96431, d97659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12735 q ha hb
    | true =>
      simp only [d96431, d97659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12737 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d96320 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d96432 q = 1) (hb : d97660 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96432, d97660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d96432, d97660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d96437 q = 1) (hb : d97620 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96437, d97620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12738 q ha hb
    | true =>
      simp only [d96437, d97620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d96438 q = 1) (hb : d97661 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96438, d97661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d96438, d97661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d96439 q = 1) (hb : d97662 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96439, d97662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d96439, d97662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d96440 q = 1) (hb : d97663 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96440, d97663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d96440, d97663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d96441 q = 1) (hb : d97664 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96441, d97664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96441, d97664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d96326 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d96444 q = 1) (hb : d97667 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96444, d97667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12740 q ha hb
    | true =>
      simp only [d96444, d97667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d96445 q = 1) (hb : d97668 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96445, d97668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96445, d97668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d96446 q = 1) (hb : d97669 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96446, d97669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d96446, d97669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d96447 q = 1) (hb : d97670 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96447, d97670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96447, d97670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d96331 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d96449 q = 1) (hb : d97672 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96449, d97672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12741 q ha hb
    | true =>
      simp only [d96449, d97672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d96450 q = 1) (hb : d97673 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96450, d97673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96450, d97673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d96451 q = 1) (hb : d97674 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96451, d97674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d96451, d97674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d96454 q = 1) (hb : d97676 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96454, d97676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12742 q ha hb
    | true =>
      simp only [d96454, d97676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12743 q ha hb
  have h28 (q : Pattern) (ha : d0 q = 1) (hb : d96336 q = 1) : d0 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d96455 q = 1) (hb : d97677 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96455, d97677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d96455, d97677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q hb ha
  have h30 (q : Pattern) (ha : d96457 q = 1) (hb : d97629 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96457, d97629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12744 q ha hb
    | true =>
      simp only [d96457, d97629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h31 (q : Pattern) (ha : d96458 q = 1) (hb : d97678 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96458, d97678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
    | true =>
      simp only [d96458, d97678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h32 (q : Pattern) (ha : d96459 q = 1) (hb : d97679 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96459, d97679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
    | true =>
      simp only [d96459, d97679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d96460 q = 1) (hb : d97680 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96460, d97680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d96460, d97680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  have h34 (q : Pattern) (ha : d96461 q = 1) (hb : d97681 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96461, d97681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d96461, d97681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
  have h35 (q : Pattern) (ha : d96462 q = 1) (hb : d97682 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96462, d97682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d96462, d97682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  exact h35 p ha hb
theorem andIntro12746 (p : Pattern) (ha : d96469 p = 1) (hb : d97684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d96230 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d96464 q = 1) (hb : d97620 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96464, d97620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12737 q ha hb
    | true =>
      simp only [d96464, d97620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d96465 q = 1) (hb : d97621 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96465, d97621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96465, d97621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d96466 q = 1) (hb : d97622 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96466, d97622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96466, d97622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96467 q = 1) (hb : d97623 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96467, d97623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96467, d97623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96468 q = 1) (hb : d97624 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96468, d97624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96468, d97624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d96285 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d96469 q = 1) (hb : d97684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96469, d97684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96469, d97684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro12747 (p : Pattern) (ha : d96476 p = 1) (hb : d97691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96454 q = 1) (hb : d97676 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96454, d97676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12742 q ha hb
    | true =>
      simp only [d96454, d97676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12743 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d96336 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d96455 q = 1) (hb : d97677 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96455, d97677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d96455, d97677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d96457 q = 1) (hb : d97629 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96457, d97629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12744 q ha hb
    | true =>
      simp only [d96457, d97629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96458 q = 1) (hb : d97678 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96458, d97678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96458, d97678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96459 q = 1) (hb : d97679 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96459, d97679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96459, d97679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d96474 q = 1) (hb : d97689 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96474, d97689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96474, d97689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d96475 q = 1) (hb : d97690 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96475, d97690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96475, d97690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d96476 q = 1) (hb : d97691 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96476, d97691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96476, d97691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro12748 (p : Pattern) (ha : d12386 p = 1) (hb : d52182 p = 1) : d0 p = 1 := by
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
  have h7 (q : Pattern) (ha : d226 q = 1) (hb : d52044 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
  have h8 (q : Pattern) (ha : d139 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
    | true =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d227 q = 1) (hb : d52045 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d227, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d140 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d228 q = 1) (hb : d52046 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d228, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d229 q = 1) (hb : d52047 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d229, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d416 q = 1) (hb : d52182 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d416, d52182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d416, d52182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52182 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d12386 q = 1) (hb : d52182 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro12749 (p : Pattern) (ha : d96488 p = 1) (hb : d97699 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d96486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12387 q = 1) (hb : d96484 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12387, d96484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12748 q ha hb
    | true =>
      simp only [d12387, d96484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12720 q ha hb
  have h3 (q : Pattern) (ha : d12388 q = 1) (hb : d96485 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12388, d96485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12388, d96485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12389 q = 1) (hb : d96486 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12389, d96486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12389, d96486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96486 q = 1) (hb : d97697 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d97697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d96358 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6079 q = 1) (hb : d96356 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d96356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12720 q ha hb
    | true =>
      simp only [d6079, d96356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12701 q ha hb
  have h8 (q : Pattern) (ha : d6080 q = 1) (hb : d96357 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d96357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6080, d96357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6081 q = 1) (hb : d96358 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d96358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6081, d96358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d96358 q = 1) (hb : d97585 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d97585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d97585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d96487 q = 1) (hb : d97698 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96487, d97698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96487, d97698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d96488 q = 1) (hb : d97699 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96488, d97699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d96488, d97699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h12 p ha hb
end NetHack.Soko22Hazard87
