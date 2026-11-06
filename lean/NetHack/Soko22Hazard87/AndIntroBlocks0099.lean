import NetHack.Soko22Hazard87.AndIntroBlocks0098
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro24750 (p : Pattern) (ha : d10909 p = 1) (hb : d107483 p = 1) : d110776 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d107483 q = 1) : d110663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24743 q ha hb
    | true =>
      simp only [d10866, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d107483 q = 1) : d110664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10871 q = 1) (hb : d107483 q = 1) : d10871 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10872 q = 1) (hb : d107483 q = 1) : d110746 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10907 q = 1) (hb : d107483 q = 1) : d110774 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10907, d110774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10907, d110774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10908 q = 1) (hb : d107483 q = 1) : d110775 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10908, d110775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10908, d110775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10909 q = 1) (hb : d107483 q = 1) : d110776 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10909, d110776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10909, d110776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24751 (p : Pattern) (ha : d10921 p = 1) (hb : d107483 p = 1) : d110781 p = 1 := by
  have h0 (q : Pattern) (ha : d10919 q = 1) (hb : d85721 q = 1) : d10919 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10745 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10920 q = 1) (hb : d107483 q = 1) : d110780 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10920, d107483, d110780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10920, d107483, d110780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10921 q = 1) (hb : d107483 q = 1) : d110781 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10921, d110781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10921, d110781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro24752 (p : Pattern) (ha : d10927 p = 1) (hb : d107483 p = 1) : d110787 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10922 q = 1) (hb : d107483 q = 1) : d110782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10922, d110782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24751 q ha hb
    | true =>
      simp only [d10922, d110782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10923 q = 1) (hb : d107483 q = 1) : d110783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10923, d110783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10923, d110783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10866 q = 1) (hb : d107483 q = 1) : d110663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24743 q ha hb
    | true =>
      simp only [d10866, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10867 q = 1) (hb : d107483 q = 1) : d110664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10924 q = 1) (hb : d107483 q = 1) : d110784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10924, d110784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10924, d110784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10925 q = 1) (hb : d107483 q = 1) : d110785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10925, d110785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10925, d110785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10926 q = 1) (hb : d107483 q = 1) : d110786 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10926, d110786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10926, d110786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10927 q = 1) (hb : d107483 q = 1) : d110787 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10927, d110787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10927, d110787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24753 (p : Pattern) (ha : d10955 p = 1) (hb : d107483 p = 1) : d110793 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d107483 q = 1) : d110663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24743 q ha hb
    | true =>
      simp only [d10866, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d107483 q = 1) : d110664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10952 q = 1) (hb : d107483 q = 1) : d110790 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10952, d110790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10952, d110790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10953 q = 1) (hb : d107483 q = 1) : d110791 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10953, d110791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10953, d110791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10954 q = 1) (hb : d107483 q = 1) : d110792 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10954, d110792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10954, d110792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10955 q = 1) (hb : d107483 q = 1) : d110793 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10955, d110793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10955, d110793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24754 (p : Pattern) (ha : d107483 p = 1) (hb : d108861 p = 1) : d110799 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10902 q = 1) (hb : d107483 q = 1) : d10902 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10903 q = 1) (hb : d107483 q = 1) : d110770 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10903, d110770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24749 q ha hb
    | true =>
      simp only [d10903, d110770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10904 q = 1) (hb : d107483 q = 1) : d110771 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10904, d110771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10904, d110771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10905 q = 1) (hb : d107483 q = 1) : d110772 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10905, d110772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10905, d110772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10906 q = 1) (hb : d107483 q = 1) : d110773 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10906, d110773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10906, d110773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10912 q = 1) (hb : d107483 q = 1) : d10912 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10913 q = 1) (hb : d107483 q = 1) : d110777 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10913, d110777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24750 q ha hb
    | true =>
      simp only [d10913, d110777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10914 q = 1) (hb : d107483 q = 1) : d110778 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10914, d110778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10914, d110778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10915 q = 1) (hb : d107483 q = 1) : d110779 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10915, d110779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10915, d110779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10928 q = 1) (hb : d107483 q = 1) : d110788 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10928, d110788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24752 q ha hb
    | true =>
      simp only [d10928, d110788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24744 q ha hb
  have h11 (q : Pattern) (ha : d107483 q = 1) (hb : d108857 q = 1) : d110789 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108857, d110789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108857, d110789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d10956 q = 1) (hb : d107483 q = 1) : d110794 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10956, d110794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24753 q ha hb
    | true =>
      simp only [d10956, d110794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d10957 q = 1) (hb : d107483 q = 1) : d110795 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10957, d110795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10957, d110795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d107483 q = 1) (hb : d108858 q = 1) : d110796 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108858, d110796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108858, d110796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d107483 q = 1) (hb : d108859 q = 1) : d110797 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108859, d110797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108859, d110797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107483 q = 1) (hb : d108860 q = 1) : d110798 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108860, d110798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d108860, d110798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d107483 q = 1) (hb : d108861 q = 1) : d110799 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108861, d110799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108861, d110799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro24755 (p : Pattern) (ha : d10962 p = 1) (hb : d107483 p = 1) : d110800 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d107483 q = 1) : d110663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24743 q ha hb
    | true =>
      simp only [d10866, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d107483 q = 1) : d110664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10871 q = 1) (hb : d107483 q = 1) : d10871 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10872 q = 1) (hb : d107483 q = 1) : d110746 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10873 q = 1) (hb : d107483 q = 1) : d110747 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10873, d110747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10873, d110747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10899 q = 1) (hb : d107483 q = 1) : d110768 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10899, d110768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10899, d110768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10962 q = 1) (hb : d107483 q = 1) : d110800 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10962, d110800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10962, d110800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro24756 (p : Pattern) (ha : d10968 p = 1) (hb : d107483 p = 1) : d110805 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d107483 q = 1) : d110663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24743 q ha hb
    | true =>
      simp only [d10866, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d107483 q = 1) : d110664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10871 q = 1) (hb : d107483 q = 1) : d10871 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10872 q = 1) (hb : d107483 q = 1) : d110746 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10907 q = 1) (hb : d107483 q = 1) : d110774 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10907, d110774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10907, d110774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10908 q = 1) (hb : d107483 q = 1) : d110775 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10908, d110775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10908, d110775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10968 q = 1) (hb : d107483 q = 1) : d110805 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10968, d110805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10968, d110805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro24757 (p : Pattern) (ha : d10973 p = 1) (hb : d107483 p = 1) : d110809 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10922 q = 1) (hb : d107483 q = 1) : d110782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10922, d110782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24751 q ha hb
    | true =>
      simp only [d10922, d110782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10923 q = 1) (hb : d107483 q = 1) : d110783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10923, d110783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10923, d110783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10866 q = 1) (hb : d107483 q = 1) : d110663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24743 q ha hb
    | true =>
      simp only [d10866, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10867 q = 1) (hb : d107483 q = 1) : d110664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10924 q = 1) (hb : d107483 q = 1) : d110784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10924, d110784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10924, d110784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10925 q = 1) (hb : d107483 q = 1) : d110785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10925, d110785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10925, d110785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10926 q = 1) (hb : d107483 q = 1) : d110786 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10926, d110786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10926, d110786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10973 q = 1) (hb : d107483 q = 1) : d110809 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10973, d110809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10973, d110809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24758 (p : Pattern) (ha : d10979 p = 1) (hb : d107483 p = 1) : d110812 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d107483 q = 1) : d110663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24743 q ha hb
    | true =>
      simp only [d10866, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d107483 q = 1) : d110664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10952 q = 1) (hb : d107483 q = 1) : d110790 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10952, d110790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10952, d110790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10953 q = 1) (hb : d107483 q = 1) : d110791 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10953, d110791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10953, d110791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10954 q = 1) (hb : d107483 q = 1) : d110792 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10954, d110792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10954, d110792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10979 q = 1) (hb : d107483 q = 1) : d110812 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10979, d110812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10979, d110812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24759 (p : Pattern) (ha : d107483 p = 1) (hb : d108866 p = 1) : d110818 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10902 q = 1) (hb : d107483 q = 1) : d10902 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10903 q = 1) (hb : d107483 q = 1) : d110770 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10903, d110770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24749 q ha hb
    | true =>
      simp only [d10903, d110770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10904 q = 1) (hb : d107483 q = 1) : d110771 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10904, d110771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10904, d110771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10905 q = 1) (hb : d107483 q = 1) : d110772 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10905, d110772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10905, d110772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10906 q = 1) (hb : d107483 q = 1) : d110773 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10906, d110773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10906, d110773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10912 q = 1) (hb : d107483 q = 1) : d10912 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10913 q = 1) (hb : d107483 q = 1) : d110777 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10913, d110777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24750 q ha hb
    | true =>
      simp only [d10913, d110777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10914 q = 1) (hb : d107483 q = 1) : d110778 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10914, d110778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10914, d110778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10915 q = 1) (hb : d107483 q = 1) : d110779 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10915, d110779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10915, d110779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10928 q = 1) (hb : d107483 q = 1) : d110788 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10928, d110788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24752 q ha hb
    | true =>
      simp only [d10928, d110788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24744 q ha hb
  have h11 (q : Pattern) (ha : d107483 q = 1) (hb : d108857 q = 1) : d110789 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108857, d110789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108857, d110789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d10956 q = 1) (hb : d107483 q = 1) : d110794 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10956, d110794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24753 q ha hb
    | true =>
      simp only [d10956, d110794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d10957 q = 1) (hb : d107483 q = 1) : d110795 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10957, d110795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10957, d110795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d107483 q = 1) (hb : d108858 q = 1) : d110796 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108858, d110796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108858, d110796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d107483 q = 1) (hb : d108859 q = 1) : d110797 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108859, d110797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108859, d110797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107483 q = 1) (hb : d108860 q = 1) : d110798 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108860, d110798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d108860, d110798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10963 q = 1) (hb : d107483 q = 1) : d10963 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d10964 q = 1) (hb : d107483 q = 1) : d110801 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10964, d110801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24755 q ha hb
    | true =>
      simp only [d10964, d110801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10965 q = 1) (hb : d107483 q = 1) : d110802 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10965, d110802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10965, d110802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10966 q = 1) (hb : d107483 q = 1) : d110803 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10966, d110803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10966, d110803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d10967 q = 1) (hb : d107483 q = 1) : d110804 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10967, d110804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10967, d110804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d10969 q = 1) (hb : d107483 q = 1) : d10969 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d10970 q = 1) (hb : d107483 q = 1) : d110806 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10970, d110806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24756 q ha hb
    | true =>
      simp only [d10970, d110806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d10971 q = 1) (hb : d107483 q = 1) : d110807 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10971, d110807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10971, d110807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d10972 q = 1) (hb : d107483 q = 1) : d110808 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10972, d110808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d10972, d110808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d10974 q = 1) (hb : d107483 q = 1) : d110810 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10974, d110810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24757 q ha hb
    | true =>
      simp only [d10974, d110810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24746 q ha hb
  have h27 (q : Pattern) (ha : d107483 q = 1) (hb : d108862 q = 1) : d110811 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108862, d110811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
    | true =>
      simp only [d108862, d110811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d10980 q = 1) (hb : d107483 q = 1) : d110813 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10980, d110813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24758 q ha hb
    | true =>
      simp only [d10980, d110813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d10981 q = 1) (hb : d107483 q = 1) : d110814 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10981, d110814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d10981, d110814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d107483 q = 1) (hb : d108863 q = 1) : d110815 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108863, d110815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d108863, d110815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d107483 q = 1) (hb : d108864 q = 1) : d110816 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108864, d110816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d108864, d110816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d107483 q = 1) (hb : d108865 q = 1) : d110817 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108865, d110817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d108865, d110817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d107483 q = 1) (hb : d108866 q = 1) : d110818 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108866, d110818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108866, d110818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro24760 (p : Pattern) (ha : d107483 p = 1) (hb : d108873 p = 1) : d110827 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10974 q = 1) (hb : d107483 q = 1) : d110810 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10974, d110810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24757 q ha hb
    | true =>
      simp only [d10974, d110810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24746 q ha hb
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d108862 q = 1) : d110811 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108862, d110811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108862, d110811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d10980 q = 1) (hb : d107483 q = 1) : d110813 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10980, d110813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24758 q ha hb
    | true =>
      simp only [d10980, d110813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10981 q = 1) (hb : d107483 q = 1) : d110814 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10981, d110814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10981, d110814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d108863 q = 1) : d110815 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108863, d110815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108863, d110815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d108871 q = 1) : d110825 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108871, d110825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108871, d110825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107483 q = 1) (hb : d108872 q = 1) : d110826 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108872, d110826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108872, d110826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107483 q = 1) (hb : d108873 q = 1) : d110827 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108873, d110827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108873, d110827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24761 (p : Pattern) (ha : d11018 p = 1) (hb : d107483 p = 1) : d110834 p = 1 := by
  have h0 (q : Pattern) (ha : d11016 q = 1) (hb : d85721 q = 1) : d11016 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10817 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11017 q = 1) (hb : d107483 q = 1) : d110833 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11017, d107483, d110833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11017, d107483, d110833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11018 q = 1) (hb : d107483 q = 1) : d110834 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11018, d110834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11018, d110834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro24762 (p : Pattern) (ha : d11023 p = 1) (hb : d107483 p = 1) : d110715 p = 1 := by
  have h0 (q : Pattern) (ha : d10817 q = 1) (hb : d85721 q = 1) : d10817 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11021 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11022 q = 1) (hb : d107483 q = 1) : d110714 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11022, d107483, d110714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11022, d107483, d110714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11023 q = 1) (hb : d107483 q = 1) : d110715 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11023, d110715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11023, d110715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro24763 (p : Pattern) (ha : d11029 p = 1) (hb : d107483 p = 1) : d110840 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11019 q = 1) (hb : d107483 q = 1) : d110835 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11019, d110835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24761 q ha hb
    | true =>
      simp only [d11019, d110835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11020 q = 1) (hb : d107483 q = 1) : d110836 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11020, d110836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11020, d110836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11024 q = 1) (hb : d107483 q = 1) : d110716 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11024, d110716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24762 q ha hb
    | true =>
      simp only [d11024, d110716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11025 q = 1) (hb : d107483 q = 1) : d110717 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11025, d110717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11025, d110717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11026 q = 1) (hb : d107483 q = 1) : d110837 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11026, d110837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11026, d110837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11027 q = 1) (hb : d107483 q = 1) : d110838 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11027, d110838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11027, d110838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11028 q = 1) (hb : d107483 q = 1) : d110839 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11028, d110839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11028, d110839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11029 q = 1) (hb : d107483 q = 1) : d110840 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11029, d110840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11029, d110840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24764 (p : Pattern) (ha : d11037 p = 1) (hb : d107483 p = 1) : d110844 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11024 q = 1) (hb : d107483 q = 1) : d110716 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11024, d110716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24762 q ha hb
    | true =>
      simp only [d11024, d110716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11025 q = 1) (hb : d107483 q = 1) : d110717 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11025, d110717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11025, d110717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11033 q = 1) (hb : d107483 q = 1) : d11033 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11034 q = 1) (hb : d107483 q = 1) : d110841 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11034, d110841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11034, d110841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11035 q = 1) (hb : d107483 q = 1) : d110842 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11035, d110842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11035, d110842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11036 q = 1) (hb : d107483 q = 1) : d110843 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11036, d110843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11036, d110843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11037 q = 1) (hb : d107483 q = 1) : d110844 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11037, d110844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11037, d110844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro24765 (p : Pattern) (ha : d11065 p = 1) (hb : d107483 p = 1) : d110850 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11024 q = 1) (hb : d107483 q = 1) : d110716 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11024, d110716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24762 q ha hb
    | true =>
      simp only [d11024, d110716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11025 q = 1) (hb : d107483 q = 1) : d110717 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11025, d110717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11025, d110717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11062 q = 1) (hb : d107483 q = 1) : d110847 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11062, d110847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11062, d110847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11063 q = 1) (hb : d107483 q = 1) : d110848 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11063, d110848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11063, d110848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11064 q = 1) (hb : d107483 q = 1) : d110849 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11064, d110849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11064, d110849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11065 q = 1) (hb : d107483 q = 1) : d110850 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11065, d110850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11065, d110850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24766 (p : Pattern) (ha : d107483 p = 1) (hb : d108883 p = 1) : d110856 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11038 q = 1) (hb : d107483 q = 1) : d110845 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11038, d110845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24763 q ha hb
    | true =>
      simp only [d11038, d110845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24764 q ha hb
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d108879 q = 1) : d110846 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108879, d110846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108879, d110846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d11066 q = 1) (hb : d107483 q = 1) : d110851 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11066, d110851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24765 q ha hb
    | true =>
      simp only [d11066, d110851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11067 q = 1) (hb : d107483 q = 1) : d110852 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11067, d110852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11067, d110852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d108880 q = 1) : d110853 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108880, d110853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108880, d110853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d108881 q = 1) : d110854 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108881, d110854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108881, d110854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107483 q = 1) (hb : d108882 q = 1) : d110855 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108882, d110855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108882, d110855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107483 q = 1) (hb : d108883 q = 1) : d110856 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108883, d110856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108883, d110856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24767 (p : Pattern) (ha : d107483 p = 1) (hb : d108889 p = 1) : d110862 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10886 q = 1) (hb : d107483 q = 1) : d110756 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10886, d110756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10886, d110756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24745 q ha hb
  have h2 (q : Pattern) (ha : d10887 q = 1) (hb : d107483 q = 1) : d110757 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10887, d110757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10887, d110757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10896 q = 1) (hb : d107483 q = 1) : d110765 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10896, d110765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24745 q ha hb
    | true =>
      simp only [d10896, d110765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24747 q ha hb
  have h4 (q : Pattern) (ha : d10897 q = 1) (hb : d107483 q = 1) : d110766 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10897, d110766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10897, d110766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10898 q = 1) (hb : d107483 q = 1) : d110767 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d10898, d110767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10898, d110767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d108867 q = 1) : d110819 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108867, d110819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24754 q ha hb
    | true =>
      simp only [d108867, d110819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24759 q ha hb
  have h7 (q : Pattern) (ha : d10998 q = 1) (hb : d107483 q = 1) : d10998 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10999 q = 1) (hb : d107483 q = 1) : d110821 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10999, d110821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24748 q ha hb
    | true =>
      simp only [d10999, d110821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107483 q = 1) (hb : d108868 q = 1) : d110822 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108868, d110822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108868, d110822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d107483 q = 1) (hb : d108869 q = 1) : d110823 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108869, d110823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108869, d110823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d107483 q = 1) (hb : d108870 q = 1) : d110824 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108870, d110824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d108870, d110824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d107483 q = 1) (hb : d108874 q = 1) : d110828 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108874, d110828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108874, d110828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24760 q ha hb
  have h13 (q : Pattern) (ha : d11008 q = 1) (hb : d107483 q = 1) : d11008 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d107483 q = 1) (hb : d108875 q = 1) : d110829 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108875, d110829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108875, d110829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d107483 q = 1) (hb : d108876 q = 1) : d110830 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108876, d110830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108876, d110830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d107483 q = 1) (hb : d108877 q = 1) : d110831 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108877, d110831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108877, d110831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d107483 q = 1) (hb : d108878 q = 1) : d110832 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108878, d110832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108878, d110832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d107483 q = 1) (hb : d108884 q = 1) : d110857 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108884, d110857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108884, d110857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24766 q ha hb
  have h19 (q : Pattern) (ha : d11083 q = 1) (hb : d107483 q = 1) : d11083 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d107483 q = 1) (hb : d108885 q = 1) : d110858 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108885, d110858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d108885, d110858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d107483 q = 1) (hb : d108886 q = 1) : d110859 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108886, d110859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d108886, d110859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d107483 q = 1) (hb : d108887 q = 1) : d110860 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108887, d110860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108887, d110860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d107483 q = 1) (hb : d108888 q = 1) : d110861 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108888, d110861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d108888, d110861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d107483 q = 1) (hb : d108889 q = 1) : d110862 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108889, d110862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108889, d110862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro24768 (p : Pattern) (ha : d107483 p = 1) (hb : d108895 p = 1) : d110868 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107483 q = 1) (hb : d108890 q = 1) : d110863 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108890, d110863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108890, d110863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24767 q ha hb
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d108891 q = 1) : d110864 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108891, d110864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108891, d110864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d108892 q = 1) : d110865 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108892, d110865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108892, d110865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d108893 q = 1) : d110866 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108893, d110866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108893, d110866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d108894 q = 1) : d110867 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108894, d110867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108894, d110867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d108895 q = 1) : d110868 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108895, d110868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108895, d110868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24769 (p : Pattern) (ha : d11105 p = 1) (hb : d107483 p = 1) : d110871 p = 1 := by
  have h0 (q : Pattern) (ha : d11102 q = 1) (hb : d85721 q = 1) : d11102 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11103 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11104 q = 1) (hb : d107483 q = 1) : d110870 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11104, d107483, d110870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11104, d107483, d110870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11105 q = 1) (hb : d107483 q = 1) : d110871 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11105, d110871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11105, d110871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro24770 (p : Pattern) (ha : d11115 p = 1) (hb : d107483 p = 1) : d110877 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d107483 q = 1) : d110872 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24769 q ha hb
    | true =>
      simp only [d11106, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d107483 q = 1) : d110873 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11111 q = 1) (hb : d107483 q = 1) : d11111 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11112 q = 1) (hb : d107483 q = 1) : d110874 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11113 q = 1) (hb : d107483 q = 1) : d110875 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11113, d110875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11113, d110875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11114 q = 1) (hb : d107483 q = 1) : d110876 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11114, d110876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11114, d110876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11115 q = 1) (hb : d107483 q = 1) : d110877 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11115, d110877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11115, d110877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24771 (p : Pattern) (ha : d11125 p = 1) (hb : d107483 p = 1) : d110883 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11119 q = 1) (hb : d107483 q = 1) : d11119 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11120 q = 1) (hb : d107483 q = 1) : d110878 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11120, d110878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24770 q ha hb
    | true =>
      simp only [d11120, d110878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11121 q = 1) (hb : d107483 q = 1) : d110879 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11121, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11121, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11122 q = 1) (hb : d107483 q = 1) : d110880 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11122, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11122, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11123 q = 1) (hb : d107483 q = 1) : d110881 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11123, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11123, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11124 q = 1) (hb : d107483 q = 1) : d110882 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11124, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11124, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11125 q = 1) (hb : d107483 q = 1) : d110883 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11125, d110883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11125, d110883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24772 (p : Pattern) (ha : d11128 p = 1) (hb : d107483 p = 1) : d110886 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d107483 q = 1) : d110872 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24769 q ha hb
    | true =>
      simp only [d11106, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d107483 q = 1) : d110873 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11111 q = 1) (hb : d107483 q = 1) : d11111 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11112 q = 1) (hb : d107483 q = 1) : d110874 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11113 q = 1) (hb : d107483 q = 1) : d110875 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11113, d110875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11113, d110875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11114 q = 1) (hb : d107483 q = 1) : d110876 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11114, d110876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11114, d110876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11128 q = 1) (hb : d107483 q = 1) : d110886 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11128, d110886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11128, d110886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro24773 (p : Pattern) (ha : d11135 p = 1) (hb : d107483 p = 1) : d110892 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11119 q = 1) (hb : d107483 q = 1) : d11119 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11120 q = 1) (hb : d107483 q = 1) : d110878 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11120, d110878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24770 q ha hb
    | true =>
      simp only [d11120, d110878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11121 q = 1) (hb : d107483 q = 1) : d110879 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11121, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11121, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11122 q = 1) (hb : d107483 q = 1) : d110880 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11122, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11122, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11123 q = 1) (hb : d107483 q = 1) : d110881 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11123, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11123, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11124 q = 1) (hb : d107483 q = 1) : d110882 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11124, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11124, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11129 q = 1) (hb : d107483 q = 1) : d11129 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d11130 q = 1) (hb : d107483 q = 1) : d110887 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11130, d110887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24772 q ha hb
    | true =>
      simp only [d11130, d110887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11131 q = 1) (hb : d107483 q = 1) : d110888 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11131, d110888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11131, d110888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11132 q = 1) (hb : d107483 q = 1) : d110889 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11132, d110889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11132, d110889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11133 q = 1) (hb : d107483 q = 1) : d110890 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11133, d110890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11133, d110890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11134 q = 1) (hb : d107483 q = 1) : d110891 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11134, d110891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11134, d110891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11135 q = 1) (hb : d107483 q = 1) : d110892 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11135, d110892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11135, d110892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro24774 (p : Pattern) (ha : d11243 p = 1) (hb : d107483 p = 1) : d110948 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11119 q = 1) (hb : d107483 q = 1) : d11119 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11120 q = 1) (hb : d107483 q = 1) : d110878 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11120, d110878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24770 q ha hb
    | true =>
      simp only [d11120, d110878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11121 q = 1) (hb : d107483 q = 1) : d110879 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11121, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11121, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11122 q = 1) (hb : d107483 q = 1) : d110880 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11122, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11122, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11123 q = 1) (hb : d107483 q = 1) : d110881 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11123, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11123, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11124 q = 1) (hb : d107483 q = 1) : d110882 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11124, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11124, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11242 q = 1) (hb : d107483 q = 1) : d11242 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d11243 q = 1) (hb : d107483 q = 1) : d110948 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11243, d110948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11243, d110948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24775 (p : Pattern) (ha : d11140 p = 1) (hb : d107483 p = 1) : d110897 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d107483 q = 1) : d110872 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24769 q ha hb
    | true =>
      simp only [d11106, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d107483 q = 1) : d110873 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11111 q = 1) (hb : d107483 q = 1) : d11111 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11112 q = 1) (hb : d107483 q = 1) : d110874 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11113 q = 1) (hb : d107483 q = 1) : d110875 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11113, d110875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11113, d110875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11139 q = 1) (hb : d107483 q = 1) : d110896 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11139, d110896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11139, d110896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11140 q = 1) (hb : d107483 q = 1) : d110897 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11140, d110897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11140, d110897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24776 (p : Pattern) (ha : d11149 p = 1) (hb : d107483 p = 1) : d110904 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d107483 q = 1) : d110872 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24769 q ha hb
    | true =>
      simp only [d11106, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d107483 q = 1) : d110873 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11111 q = 1) (hb : d107483 q = 1) : d11111 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11112 q = 1) (hb : d107483 q = 1) : d110874 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11147 q = 1) (hb : d107483 q = 1) : d110902 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11147, d110902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11147, d110902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11148 q = 1) (hb : d107483 q = 1) : d110903 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11148, d110903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11148, d110903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11149 q = 1) (hb : d107483 q = 1) : d110904 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11149, d110904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11149, d110904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24777 (p : Pattern) (ha : d11161 p = 1) (hb : d107483 p = 1) : d110909 p = 1 := by
  have h0 (q : Pattern) (ha : d11159 q = 1) (hb : d85721 q = 1) : d11159 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11102 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11160 q = 1) (hb : d107483 q = 1) : d110908 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11160, d107483, d110908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11160, d107483, d110908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11161 q = 1) (hb : d107483 q = 1) : d110909 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11161, d110909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11161, d110909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro24778 (p : Pattern) (ha : d11167 p = 1) (hb : d107483 p = 1) : d110915 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11162 q = 1) (hb : d107483 q = 1) : d110910 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11162, d110910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24777 q ha hb
    | true =>
      simp only [d11162, d110910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11163 q = 1) (hb : d107483 q = 1) : d110911 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11163, d110911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11163, d110911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11106 q = 1) (hb : d107483 q = 1) : d110872 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24769 q ha hb
    | true =>
      simp only [d11106, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11107 q = 1) (hb : d107483 q = 1) : d110873 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11164 q = 1) (hb : d107483 q = 1) : d110912 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11164, d110912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11164, d110912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11165 q = 1) (hb : d107483 q = 1) : d110913 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11165, d110913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11165, d110913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11166 q = 1) (hb : d107483 q = 1) : d110914 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11166, d110914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11166, d110914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11167 q = 1) (hb : d107483 q = 1) : d110915 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11167, d110915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11167, d110915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24779 (p : Pattern) (ha : d11200 p = 1) (hb : d107483 p = 1) : d110871 p = 1 := by
  have h0 (q : Pattern) (ha : d11102 q = 1) (hb : d85721 q = 1) : d11102 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11198 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11199 q = 1) (hb : d107483 q = 1) : d110870 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11199, d107483, d110870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11199, d107483, d110870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11200 q = 1) (hb : d107483 q = 1) : d110871 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11200, d110871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11200, d110871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro24780 (p : Pattern) (ha : d11206 p = 1) (hb : d107483 p = 1) : d110921 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11201 q = 1) (hb : d107483 q = 1) : d110872 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11201, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24779 q ha hb
    | true =>
      simp only [d11201, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11202 q = 1) (hb : d107483 q = 1) : d110873 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11202, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11202, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11203 q = 1) (hb : d107483 q = 1) : d110918 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11203, d110918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11203, d110918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11204 q = 1) (hb : d107483 q = 1) : d110919 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11204, d110919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11204, d110919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11205 q = 1) (hb : d107483 q = 1) : d110920 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11205, d110920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11205, d110920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11206 q = 1) (hb : d107483 q = 1) : d110921 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11206, d110921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11206, d110921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24781 (p : Pattern) (ha : d107483 p = 1) (hb : d108901 p = 1) : d110927 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11142 q = 1) (hb : d107483 q = 1) : d11142 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11143 q = 1) (hb : d107483 q = 1) : d110898 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11143, d110898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24775 q ha hb
    | true =>
      simp only [d11143, d110898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11144 q = 1) (hb : d107483 q = 1) : d110899 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11144, d110899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11144, d110899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11145 q = 1) (hb : d107483 q = 1) : d110900 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11145, d110900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11145, d110900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11146 q = 1) (hb : d107483 q = 1) : d110901 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11146, d110901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11146, d110901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11152 q = 1) (hb : d107483 q = 1) : d11152 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11153 q = 1) (hb : d107483 q = 1) : d110905 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11153, d110905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24776 q ha hb
    | true =>
      simp only [d11153, d110905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11154 q = 1) (hb : d107483 q = 1) : d110906 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11154, d110906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11154, d110906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11155 q = 1) (hb : d107483 q = 1) : d110907 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11155, d110907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11155, d110907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11168 q = 1) (hb : d107483 q = 1) : d110916 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11168, d110916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24778 q ha hb
    | true =>
      simp only [d11168, d110916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24770 q ha hb
  have h11 (q : Pattern) (ha : d107483 q = 1) (hb : d108897 q = 1) : d110917 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108897, d110917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108897, d110917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d11207 q = 1) (hb : d107483 q = 1) : d110922 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11207, d110922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24780 q ha hb
    | true =>
      simp only [d11207, d110922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d11208 q = 1) (hb : d107483 q = 1) : d110923 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11208, d110923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d11208, d110923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d107483 q = 1) (hb : d108898 q = 1) : d110924 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108898, d110924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108898, d110924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d107483 q = 1) (hb : d108899 q = 1) : d110925 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108899, d110925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108899, d110925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107483 q = 1) (hb : d108900 q = 1) : d110926 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108900, d110926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d108900, d110926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d107483 q = 1) (hb : d108901 q = 1) : d110927 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108901, d110927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108901, d110927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro24782 (p : Pattern) (ha : d11213 p = 1) (hb : d107483 p = 1) : d110928 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d107483 q = 1) : d110872 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24769 q ha hb
    | true =>
      simp only [d11106, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d107483 q = 1) : d110873 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11111 q = 1) (hb : d107483 q = 1) : d11111 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11112 q = 1) (hb : d107483 q = 1) : d110874 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11113 q = 1) (hb : d107483 q = 1) : d110875 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11113, d110875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11113, d110875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11139 q = 1) (hb : d107483 q = 1) : d110896 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11139, d110896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11139, d110896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11213 q = 1) (hb : d107483 q = 1) : d110928 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11213, d110928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11213, d110928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro24783 (p : Pattern) (ha : d11219 p = 1) (hb : d107483 p = 1) : d110933 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d107483 q = 1) : d110872 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24769 q ha hb
    | true =>
      simp only [d11106, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d107483 q = 1) : d110873 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11111 q = 1) (hb : d107483 q = 1) : d11111 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11112 q = 1) (hb : d107483 q = 1) : d110874 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11147 q = 1) (hb : d107483 q = 1) : d110902 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11147, d110902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11147, d110902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11148 q = 1) (hb : d107483 q = 1) : d110903 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11148, d110903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11148, d110903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11219 q = 1) (hb : d107483 q = 1) : d110933 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11219, d110933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11219, d110933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro24784 (p : Pattern) (ha : d11224 p = 1) (hb : d107483 p = 1) : d110937 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11162 q = 1) (hb : d107483 q = 1) : d110910 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11162, d110910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24777 q ha hb
    | true =>
      simp only [d11162, d110910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11163 q = 1) (hb : d107483 q = 1) : d110911 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11163, d110911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11163, d110911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11106 q = 1) (hb : d107483 q = 1) : d110872 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24769 q ha hb
    | true =>
      simp only [d11106, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11107 q = 1) (hb : d107483 q = 1) : d110873 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11164 q = 1) (hb : d107483 q = 1) : d110912 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11164, d110912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11164, d110912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11165 q = 1) (hb : d107483 q = 1) : d110913 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11165, d110913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11165, d110913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11166 q = 1) (hb : d107483 q = 1) : d110914 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11166, d110914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11166, d110914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11224 q = 1) (hb : d107483 q = 1) : d110937 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11224, d110937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11224, d110937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24785 (p : Pattern) (ha : d11230 p = 1) (hb : d107483 p = 1) : d110940 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11201 q = 1) (hb : d107483 q = 1) : d110872 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11201, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24779 q ha hb
    | true =>
      simp only [d11201, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11202 q = 1) (hb : d107483 q = 1) : d110873 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11202, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11202, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11203 q = 1) (hb : d107483 q = 1) : d110918 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11203, d110918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11203, d110918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11204 q = 1) (hb : d107483 q = 1) : d110919 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11204, d110919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11204, d110919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11205 q = 1) (hb : d107483 q = 1) : d110920 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11205, d110920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11205, d110920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11230 q = 1) (hb : d107483 q = 1) : d110940 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11230, d110940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11230, d110940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24786 (p : Pattern) (ha : d107483 p = 1) (hb : d108906 p = 1) : d110946 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11142 q = 1) (hb : d107483 q = 1) : d11142 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11143 q = 1) (hb : d107483 q = 1) : d110898 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11143, d110898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24775 q ha hb
    | true =>
      simp only [d11143, d110898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11144 q = 1) (hb : d107483 q = 1) : d110899 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11144, d110899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11144, d110899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11145 q = 1) (hb : d107483 q = 1) : d110900 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11145, d110900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11145, d110900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11146 q = 1) (hb : d107483 q = 1) : d110901 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11146, d110901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11146, d110901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11152 q = 1) (hb : d107483 q = 1) : d11152 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11153 q = 1) (hb : d107483 q = 1) : d110905 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11153, d110905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24776 q ha hb
    | true =>
      simp only [d11153, d110905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11154 q = 1) (hb : d107483 q = 1) : d110906 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11154, d110906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11154, d110906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11155 q = 1) (hb : d107483 q = 1) : d110907 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11155, d110907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11155, d110907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11168 q = 1) (hb : d107483 q = 1) : d110916 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11168, d110916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24778 q ha hb
    | true =>
      simp only [d11168, d110916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24770 q ha hb
  have h11 (q : Pattern) (ha : d107483 q = 1) (hb : d108897 q = 1) : d110917 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108897, d110917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108897, d110917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d11207 q = 1) (hb : d107483 q = 1) : d110922 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11207, d110922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24780 q ha hb
    | true =>
      simp only [d11207, d110922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d11208 q = 1) (hb : d107483 q = 1) : d110923 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11208, d110923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d11208, d110923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d107483 q = 1) (hb : d108898 q = 1) : d110924 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108898, d110924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108898, d110924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d107483 q = 1) (hb : d108899 q = 1) : d110925 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108899, d110925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108899, d110925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107483 q = 1) (hb : d108900 q = 1) : d110926 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108900, d110926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d108900, d110926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d11214 q = 1) (hb : d107483 q = 1) : d11214 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d11215 q = 1) (hb : d107483 q = 1) : d110929 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11215, d110929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24782 q ha hb
    | true =>
      simp only [d11215, d110929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d11216 q = 1) (hb : d107483 q = 1) : d110930 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11216, d110930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11216, d110930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d11217 q = 1) (hb : d107483 q = 1) : d110931 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11217, d110931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d11217, d110931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d11218 q = 1) (hb : d107483 q = 1) : d110932 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11218, d110932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11218, d110932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d11220 q = 1) (hb : d107483 q = 1) : d11220 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d11221 q = 1) (hb : d107483 q = 1) : d110934 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11221, d110934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24783 q ha hb
    | true =>
      simp only [d11221, d110934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d11222 q = 1) (hb : d107483 q = 1) : d110935 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11222, d110935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11222, d110935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d11223 q = 1) (hb : d107483 q = 1) : d110936 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11223, d110936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d11223, d110936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d11225 q = 1) (hb : d107483 q = 1) : d110938 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11225, d110938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24784 q ha hb
    | true =>
      simp only [d11225, d110938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24772 q ha hb
  have h27 (q : Pattern) (ha : d107483 q = 1) (hb : d108902 q = 1) : d110939 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108902, d110939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
    | true =>
      simp only [d108902, d110939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d11231 q = 1) (hb : d107483 q = 1) : d110941 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11231, d110941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24785 q ha hb
    | true =>
      simp only [d11231, d110941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d11232 q = 1) (hb : d107483 q = 1) : d110942 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11232, d110942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d11232, d110942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d107483 q = 1) (hb : d108903 q = 1) : d110943 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108903, d110943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d108903, d110943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d107483 q = 1) (hb : d108904 q = 1) : d110944 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108904, d110944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d108904, d110944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d107483 q = 1) (hb : d108905 q = 1) : d110945 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108905, d110945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d108905, d110945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d107483 q = 1) (hb : d108906 q = 1) : d110946 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108906, d110946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108906, d110946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro24787 (p : Pattern) (ha : d107483 p = 1) (hb : d108913 p = 1) : d110955 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11225 q = 1) (hb : d107483 q = 1) : d110938 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11225, d110938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24784 q ha hb
    | true =>
      simp only [d11225, d110938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24772 q ha hb
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d108902 q = 1) : d110939 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108902, d110939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108902, d110939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d11231 q = 1) (hb : d107483 q = 1) : d110941 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11231, d110941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24785 q ha hb
    | true =>
      simp only [d11231, d110941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11232 q = 1) (hb : d107483 q = 1) : d110942 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11232, d110942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11232, d110942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d108903 q = 1) : d110943 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108903, d110943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108903, d110943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d108911 q = 1) : d110953 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108911, d110953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108911, d110953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107483 q = 1) (hb : d108912 q = 1) : d110954 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108912, d110954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108912, d110954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107483 q = 1) (hb : d108913 q = 1) : d110955 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108913, d110955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108913, d110955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24788 (p : Pattern) (ha : d11276 p = 1) (hb : d107483 p = 1) : d110962 p = 1 := by
  have h0 (q : Pattern) (ha : d11270 q = 1) (hb : d85721 q = 1) : d11270 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11274 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11275 q = 1) (hb : d107483 q = 1) : d110961 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11275, d107483, d110961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11275, d107483, d110961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11276 q = 1) (hb : d107483 q = 1) : d110962 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11276, d110962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11276, d110962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro24789 (p : Pattern) (ha : d11281 p = 1) (hb : d107483 p = 1) : d110966 p = 1 := by
  have h0 (q : Pattern) (ha : d11274 q = 1) (hb : d85721 q = 1) : d11274 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11279 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11280 q = 1) (hb : d107483 q = 1) : d110965 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11280, d107483, d110965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11280, d107483, d110965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11281 q = 1) (hb : d107483 q = 1) : d110966 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11281, d110966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11281, d110966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro24790 (p : Pattern) (ha : d11287 p = 1) (hb : d107483 p = 1) : d110972 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11277 q = 1) (hb : d107483 q = 1) : d110963 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11277, d110963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24788 q ha hb
    | true =>
      simp only [d11277, d110963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11278 q = 1) (hb : d107483 q = 1) : d110964 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11278, d110964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11278, d110964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11282 q = 1) (hb : d107483 q = 1) : d110967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11282, d110967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24789 q ha hb
    | true =>
      simp only [d11282, d110967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11283 q = 1) (hb : d107483 q = 1) : d110968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11283, d110968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11283, d110968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11284 q = 1) (hb : d107483 q = 1) : d110969 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11284, d110969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11284, d110969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11285 q = 1) (hb : d107483 q = 1) : d110970 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11285, d110970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11285, d110970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11286 q = 1) (hb : d107483 q = 1) : d110971 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11286, d110971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11286, d110971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11287 q = 1) (hb : d107483 q = 1) : d110972 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11287, d110972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11287, d110972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24791 (p : Pattern) (ha : d11295 p = 1) (hb : d107483 p = 1) : d110976 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11282 q = 1) (hb : d107483 q = 1) : d110967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11282, d110967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24789 q ha hb
    | true =>
      simp only [d11282, d110967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11283 q = 1) (hb : d107483 q = 1) : d110968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11283, d110968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11283, d110968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11291 q = 1) (hb : d107483 q = 1) : d11291 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11292 q = 1) (hb : d107483 q = 1) : d110973 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11292, d110973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11292, d110973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11293 q = 1) (hb : d107483 q = 1) : d110974 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11293, d110974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11293, d110974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11294 q = 1) (hb : d107483 q = 1) : d110975 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11294, d110975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11294, d110975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11295 q = 1) (hb : d107483 q = 1) : d110976 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11295, d110976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11295, d110976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro24792 (p : Pattern) (ha : d11328 p = 1) (hb : d107483 p = 1) : d110966 p = 1 := by
  have h0 (q : Pattern) (ha : d11274 q = 1) (hb : d85721 q = 1) : d11274 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11326 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11327 q = 1) (hb : d107483 q = 1) : d110965 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11327, d107483, d110965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11327, d107483, d110965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11328 q = 1) (hb : d107483 q = 1) : d110966 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11328, d110966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11328, d110966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro24793 (p : Pattern) (ha : d11334 p = 1) (hb : d107483 p = 1) : d110982 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11329 q = 1) (hb : d107483 q = 1) : d110967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11329, d110967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24792 q ha hb
    | true =>
      simp only [d11329, d110967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11330 q = 1) (hb : d107483 q = 1) : d110968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11330, d110968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11330, d110968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11331 q = 1) (hb : d107483 q = 1) : d110979 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11331, d110979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11331, d110979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11332 q = 1) (hb : d107483 q = 1) : d110980 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11332, d110980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11332, d110980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11333 q = 1) (hb : d107483 q = 1) : d110981 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11333, d110981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11333, d110981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11334 q = 1) (hb : d107483 q = 1) : d110982 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11334, d110982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11334, d110982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24794 (p : Pattern) (ha : d107483 p = 1) (hb : d108923 p = 1) : d110988 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11296 q = 1) (hb : d107483 q = 1) : d110977 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11296, d110977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24790 q ha hb
    | true =>
      simp only [d11296, d110977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24791 q ha hb
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d108919 q = 1) : d110978 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108919, d110978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108919, d110978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d11335 q = 1) (hb : d107483 q = 1) : d110983 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11335, d110983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24793 q ha hb
    | true =>
      simp only [d11335, d110983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11336 q = 1) (hb : d107483 q = 1) : d110984 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11336, d110984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11336, d110984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d108920 q = 1) : d110985 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108920, d110985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108920, d110985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d108921 q = 1) : d110986 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108921, d110986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108921, d110986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107483 q = 1) (hb : d108922 q = 1) : d110987 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108922, d110987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108922, d110987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107483 q = 1) (hb : d108923 q = 1) : d110988 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108923, d110988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108923, d110988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24795 (p : Pattern) (ha : d107483 p = 1) (hb : d108929 p = 1) : d110994 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11126 q = 1) (hb : d107483 q = 1) : d110884 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11126, d110884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11126, d110884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24771 q ha hb
  have h2 (q : Pattern) (ha : d11127 q = 1) (hb : d107483 q = 1) : d110885 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11127, d110885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11127, d110885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11136 q = 1) (hb : d107483 q = 1) : d110893 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11136, d110893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24771 q ha hb
    | true =>
      simp only [d11136, d110893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24773 q ha hb
  have h4 (q : Pattern) (ha : d11137 q = 1) (hb : d107483 q = 1) : d110894 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11137, d110894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11137, d110894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11138 q = 1) (hb : d107483 q = 1) : d110895 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11138, d110895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11138, d110895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d108907 q = 1) : d110947 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108907, d110947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24781 q ha hb
    | true =>
      simp only [d108907, d110947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24786 q ha hb
  have h7 (q : Pattern) (ha : d11249 q = 1) (hb : d107483 q = 1) : d11249 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d11250 q = 1) (hb : d107483 q = 1) : d110949 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11250, d110949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24774 q ha hb
    | true =>
      simp only [d11250, d110949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107483 q = 1) (hb : d108908 q = 1) : d110950 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108908, d110950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108908, d110950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d107483 q = 1) (hb : d108909 q = 1) : d110951 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108909, d110951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108909, d110951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d107483 q = 1) (hb : d108910 q = 1) : d110952 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108910, d110952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d108910, d110952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d107483 q = 1) (hb : d108914 q = 1) : d110956 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108914, d110956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108914, d110956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24787 q ha hb
  have h13 (q : Pattern) (ha : d11259 q = 1) (hb : d107483 q = 1) : d11259 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d107483 q = 1) (hb : d108915 q = 1) : d110957 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108915, d110957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108915, d110957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d107483 q = 1) (hb : d108916 q = 1) : d110958 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108916, d110958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108916, d110958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d107483 q = 1) (hb : d108917 q = 1) : d110959 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108917, d110959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108917, d110959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d107483 q = 1) (hb : d108918 q = 1) : d110960 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108918, d110960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108918, d110960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d107483 q = 1) (hb : d108924 q = 1) : d110989 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108924, d110989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108924, d110989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24794 q ha hb
  have h19 (q : Pattern) (ha : d11352 q = 1) (hb : d107483 q = 1) : d11352 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d107483 q = 1) (hb : d108925 q = 1) : d110990 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108925, d110990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d108925, d110990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d107483 q = 1) (hb : d108926 q = 1) : d110991 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108926, d110991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d108926, d110991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d107483 q = 1) (hb : d108927 q = 1) : d110992 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108927, d110992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108927, d110992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d107483 q = 1) (hb : d108928 q = 1) : d110993 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108928, d110993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d108928, d110993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d107483 q = 1) (hb : d108929 q = 1) : d110994 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108929, d110994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108929, d110994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro24796 (p : Pattern) (ha : d107483 p = 1) (hb : d108935 p = 1) : d111000 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107483 q = 1) (hb : d108930 q = 1) : d110995 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108930, d110995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108930, d110995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24795 q ha hb
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d108931 q = 1) : d110996 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108931, d110996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108931, d110996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d108932 q = 1) : d110997 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108932, d110997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108932, d110997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d108933 q = 1) : d110998 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108933, d110998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108933, d110998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d108934 q = 1) : d110999 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108934, d110999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108934, d110999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d108935 q = 1) : d111000 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108935, d111000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108935, d111000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24797 (p : Pattern) (ha : d11375 p = 1) (hb : d107483 p = 1) : d111004 p = 1 := by
  have h0 (q : Pattern) (ha : d11372 q = 1) (hb : d85721 q = 1) : d11372 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11373 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11374 q = 1) (hb : d107483 q = 1) : d111003 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11374, d107483, d111003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11374, d107483, d111003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11375 q = 1) (hb : d107483 q = 1) : d111004 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11375, d111004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11375, d111004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro24798 (p : Pattern) (ha : d11385 p = 1) (hb : d107483 p = 1) : d111010 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11376 q = 1) (hb : d107483 q = 1) : d111005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24797 q ha hb
    | true =>
      simp only [d11376, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11377 q = 1) (hb : d107483 q = 1) : d111006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11381 q = 1) (hb : d107483 q = 1) : d11381 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11382 q = 1) (hb : d107483 q = 1) : d111007 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11382, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11383 q = 1) (hb : d107483 q = 1) : d111008 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11383, d111008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11383, d111008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11384 q = 1) (hb : d107483 q = 1) : d111009 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11384, d111009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11384, d111009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11385 q = 1) (hb : d107483 q = 1) : d111010 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11385, d111010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11385, d111010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24799 (p : Pattern) (ha : d11395 p = 1) (hb : d107483 p = 1) : d111016 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11389 q = 1) (hb : d107483 q = 1) : d11389 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11390 q = 1) (hb : d107483 q = 1) : d111011 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11390, d111011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24798 q ha hb
    | true =>
      simp only [d11390, d111011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11391 q = 1) (hb : d107483 q = 1) : d111012 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11391, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11391, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11392 q = 1) (hb : d107483 q = 1) : d111013 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11392, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11392, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11393 q = 1) (hb : d107483 q = 1) : d111014 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11393, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11393, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11394 q = 1) (hb : d107483 q = 1) : d111015 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11394, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11394, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11395 q = 1) (hb : d107483 q = 1) : d111016 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11395, d111016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11395, d111016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24800 (p : Pattern) (ha : d11398 p = 1) (hb : d107483 p = 1) : d111019 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11376 q = 1) (hb : d107483 q = 1) : d111005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24797 q ha hb
    | true =>
      simp only [d11376, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11377 q = 1) (hb : d107483 q = 1) : d111006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11381 q = 1) (hb : d107483 q = 1) : d11381 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11382 q = 1) (hb : d107483 q = 1) : d111007 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11382, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11383 q = 1) (hb : d107483 q = 1) : d111008 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11383, d111008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11383, d111008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11384 q = 1) (hb : d107483 q = 1) : d111009 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11384, d111009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11384, d111009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11398 q = 1) (hb : d107483 q = 1) : d111019 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11398, d111019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11398, d111019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro24801 (p : Pattern) (ha : d11405 p = 1) (hb : d107483 p = 1) : d111025 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11389 q = 1) (hb : d107483 q = 1) : d11389 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11390 q = 1) (hb : d107483 q = 1) : d111011 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11390, d111011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24798 q ha hb
    | true =>
      simp only [d11390, d111011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11391 q = 1) (hb : d107483 q = 1) : d111012 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11391, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11391, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11392 q = 1) (hb : d107483 q = 1) : d111013 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11392, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11392, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11393 q = 1) (hb : d107483 q = 1) : d111014 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11393, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11393, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11394 q = 1) (hb : d107483 q = 1) : d111015 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11394, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11394, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11399 q = 1) (hb : d107483 q = 1) : d11399 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d11400 q = 1) (hb : d107483 q = 1) : d111020 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11400, d111020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24800 q ha hb
    | true =>
      simp only [d11400, d111020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11401 q = 1) (hb : d107483 q = 1) : d111021 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11401, d111021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11401, d111021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11402 q = 1) (hb : d107483 q = 1) : d111022 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11402, d111022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11402, d111022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11403 q = 1) (hb : d107483 q = 1) : d111023 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11403, d111023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11403, d111023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11404 q = 1) (hb : d107483 q = 1) : d111024 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11404, d111024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11404, d111024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11405 q = 1) (hb : d107483 q = 1) : d111025 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11405, d111025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11405, d111025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro24802 (p : Pattern) (ha : d11513 p = 1) (hb : d107483 p = 1) : d111081 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11389 q = 1) (hb : d107483 q = 1) : d11389 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11390 q = 1) (hb : d107483 q = 1) : d111011 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11390, d111011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24798 q ha hb
    | true =>
      simp only [d11390, d111011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11391 q = 1) (hb : d107483 q = 1) : d111012 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11391, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11391, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11392 q = 1) (hb : d107483 q = 1) : d111013 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11392, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11392, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11393 q = 1) (hb : d107483 q = 1) : d111014 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11393, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11393, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11394 q = 1) (hb : d107483 q = 1) : d111015 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11394, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11394, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11512 q = 1) (hb : d107483 q = 1) : d11512 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d11513 q = 1) (hb : d107483 q = 1) : d111081 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11513, d111081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11513, d111081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24803 (p : Pattern) (ha : d11410 p = 1) (hb : d107483 p = 1) : d111030 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11376 q = 1) (hb : d107483 q = 1) : d111005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24797 q ha hb
    | true =>
      simp only [d11376, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11377 q = 1) (hb : d107483 q = 1) : d111006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11381 q = 1) (hb : d107483 q = 1) : d11381 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11382 q = 1) (hb : d107483 q = 1) : d111007 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11382, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11383 q = 1) (hb : d107483 q = 1) : d111008 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11383, d111008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11383, d111008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11409 q = 1) (hb : d107483 q = 1) : d111029 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11409, d111029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11409, d111029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11410 q = 1) (hb : d107483 q = 1) : d111030 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11410, d111030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11410, d111030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24804 (p : Pattern) (ha : d11419 p = 1) (hb : d107483 p = 1) : d111037 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11376 q = 1) (hb : d107483 q = 1) : d111005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24797 q ha hb
    | true =>
      simp only [d11376, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11377 q = 1) (hb : d107483 q = 1) : d111006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11381 q = 1) (hb : d107483 q = 1) : d11381 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11382 q = 1) (hb : d107483 q = 1) : d111007 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11382, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11417 q = 1) (hb : d107483 q = 1) : d111035 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11417, d111035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11417, d111035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11418 q = 1) (hb : d107483 q = 1) : d111036 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11418, d111036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11418, d111036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11419 q = 1) (hb : d107483 q = 1) : d111037 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11419, d111037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11419, d111037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24805 (p : Pattern) (ha : d11431 p = 1) (hb : d107483 p = 1) : d111042 p = 1 := by
  have h0 (q : Pattern) (ha : d11429 q = 1) (hb : d85721 q = 1) : d11429 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11372 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11430 q = 1) (hb : d107483 q = 1) : d111041 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11430, d107483, d111041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11430, d107483, d111041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11431 q = 1) (hb : d107483 q = 1) : d111042 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11431, d111042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11431, d111042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro24806 (p : Pattern) (ha : d11437 p = 1) (hb : d107483 p = 1) : d111048 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11432 q = 1) (hb : d107483 q = 1) : d111043 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11432, d111043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24805 q ha hb
    | true =>
      simp only [d11432, d111043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11433 q = 1) (hb : d107483 q = 1) : d111044 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11433, d111044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11433, d111044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11376 q = 1) (hb : d107483 q = 1) : d111005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24797 q ha hb
    | true =>
      simp only [d11376, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11377 q = 1) (hb : d107483 q = 1) : d111006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11434 q = 1) (hb : d107483 q = 1) : d111045 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11434, d111045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11434, d111045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11435 q = 1) (hb : d107483 q = 1) : d111046 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11435, d111046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11435, d111046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11436 q = 1) (hb : d107483 q = 1) : d111047 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11436, d111047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11436, d111047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11437 q = 1) (hb : d107483 q = 1) : d111048 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11437, d111048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11437, d111048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24807 (p : Pattern) (ha : d11470 p = 1) (hb : d107483 p = 1) : d111004 p = 1 := by
  have h0 (q : Pattern) (ha : d11372 q = 1) (hb : d85721 q = 1) : d11372 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11468 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11469 q = 1) (hb : d107483 q = 1) : d111003 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11469, d107483, d111003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11469, d107483, d111003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11470 q = 1) (hb : d107483 q = 1) : d111004 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11470, d111004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11470, d111004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro24808 (p : Pattern) (ha : d11476 p = 1) (hb : d107483 p = 1) : d111054 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11471 q = 1) (hb : d107483 q = 1) : d111005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11471, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24807 q ha hb
    | true =>
      simp only [d11471, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11472 q = 1) (hb : d107483 q = 1) : d111006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11472, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11472, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11473 q = 1) (hb : d107483 q = 1) : d111051 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11473, d111051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11473, d111051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11474 q = 1) (hb : d107483 q = 1) : d111052 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11474, d111052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11474, d111052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11475 q = 1) (hb : d107483 q = 1) : d111053 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11475, d111053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11475, d111053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11476 q = 1) (hb : d107483 q = 1) : d111054 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11476, d111054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11476, d111054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24809 (p : Pattern) (ha : d107483 p = 1) (hb : d108942 p = 1) : d111060 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11412 q = 1) (hb : d107483 q = 1) : d11412 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11413 q = 1) (hb : d107483 q = 1) : d111031 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11413, d111031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24803 q ha hb
    | true =>
      simp only [d11413, d111031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11414 q = 1) (hb : d107483 q = 1) : d111032 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11414, d111032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11414, d111032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11415 q = 1) (hb : d107483 q = 1) : d111033 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11415, d111033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11415, d111033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11416 q = 1) (hb : d107483 q = 1) : d111034 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11416, d111034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11416, d111034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11422 q = 1) (hb : d107483 q = 1) : d11422 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11423 q = 1) (hb : d107483 q = 1) : d111038 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11423, d111038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24804 q ha hb
    | true =>
      simp only [d11423, d111038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11424 q = 1) (hb : d107483 q = 1) : d111039 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11424, d111039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11424, d111039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11425 q = 1) (hb : d107483 q = 1) : d111040 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11425, d111040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11425, d111040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11438 q = 1) (hb : d107483 q = 1) : d111049 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11438, d111049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24806 q ha hb
    | true =>
      simp only [d11438, d111049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24798 q ha hb
  have h11 (q : Pattern) (ha : d107483 q = 1) (hb : d108938 q = 1) : d111050 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108938, d111050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108938, d111050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d11477 q = 1) (hb : d107483 q = 1) : d111055 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11477, d111055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24808 q ha hb
    | true =>
      simp only [d11477, d111055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d11478 q = 1) (hb : d107483 q = 1) : d111056 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11478, d111056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d11478, d111056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d107483 q = 1) (hb : d108939 q = 1) : d111057 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108939, d111057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108939, d111057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d107483 q = 1) (hb : d108940 q = 1) : d111058 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108940, d111058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108940, d111058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107483 q = 1) (hb : d108941 q = 1) : d111059 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108941, d111059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d108941, d111059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d107483 q = 1) (hb : d108942 q = 1) : d111060 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108942, d111060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108942, d111060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro24810 (p : Pattern) (ha : d11483 p = 1) (hb : d107483 p = 1) : d111061 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11376 q = 1) (hb : d107483 q = 1) : d111005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24797 q ha hb
    | true =>
      simp only [d11376, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11377 q = 1) (hb : d107483 q = 1) : d111006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11381 q = 1) (hb : d107483 q = 1) : d11381 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11382 q = 1) (hb : d107483 q = 1) : d111007 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11382, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11383 q = 1) (hb : d107483 q = 1) : d111008 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11383, d111008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11383, d111008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11409 q = 1) (hb : d107483 q = 1) : d111029 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11409, d111029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11409, d111029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11483 q = 1) (hb : d107483 q = 1) : d111061 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11483, d111061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11483, d111061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro24811 (p : Pattern) (ha : d11489 p = 1) (hb : d107483 p = 1) : d111066 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11376 q = 1) (hb : d107483 q = 1) : d111005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24797 q ha hb
    | true =>
      simp only [d11376, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11377 q = 1) (hb : d107483 q = 1) : d111006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11381 q = 1) (hb : d107483 q = 1) : d11381 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11382 q = 1) (hb : d107483 q = 1) : d111007 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11382, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11417 q = 1) (hb : d107483 q = 1) : d111035 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11417, d111035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11417, d111035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11418 q = 1) (hb : d107483 q = 1) : d111036 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11418, d111036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11418, d111036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11489 q = 1) (hb : d107483 q = 1) : d111066 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11489, d111066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11489, d111066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro24812 (p : Pattern) (ha : d11494 p = 1) (hb : d107483 p = 1) : d111070 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11432 q = 1) (hb : d107483 q = 1) : d111043 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11432, d111043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24805 q ha hb
    | true =>
      simp only [d11432, d111043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11433 q = 1) (hb : d107483 q = 1) : d111044 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11433, d111044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11433, d111044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11376 q = 1) (hb : d107483 q = 1) : d111005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24797 q ha hb
    | true =>
      simp only [d11376, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11377 q = 1) (hb : d107483 q = 1) : d111006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11434 q = 1) (hb : d107483 q = 1) : d111045 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11434, d111045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11434, d111045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11435 q = 1) (hb : d107483 q = 1) : d111046 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11435, d111046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11435, d111046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11436 q = 1) (hb : d107483 q = 1) : d111047 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11436, d111047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11436, d111047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11494 q = 1) (hb : d107483 q = 1) : d111070 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11494, d111070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11494, d111070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24813 (p : Pattern) (ha : d11500 p = 1) (hb : d107483 p = 1) : d111073 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11471 q = 1) (hb : d107483 q = 1) : d111005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11471, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24807 q ha hb
    | true =>
      simp only [d11471, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11472 q = 1) (hb : d107483 q = 1) : d111006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11472, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11472, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11473 q = 1) (hb : d107483 q = 1) : d111051 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11473, d111051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11473, d111051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11474 q = 1) (hb : d107483 q = 1) : d111052 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11474, d111052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11474, d111052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11475 q = 1) (hb : d107483 q = 1) : d111053 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11475, d111053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11475, d111053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11500 q = 1) (hb : d107483 q = 1) : d111073 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11500, d111073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11500, d111073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24814 (p : Pattern) (ha : d107483 p = 1) (hb : d108947 p = 1) : d111079 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11412 q = 1) (hb : d107483 q = 1) : d11412 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11413 q = 1) (hb : d107483 q = 1) : d111031 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11413, d111031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24803 q ha hb
    | true =>
      simp only [d11413, d111031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11414 q = 1) (hb : d107483 q = 1) : d111032 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11414, d111032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11414, d111032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11415 q = 1) (hb : d107483 q = 1) : d111033 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11415, d111033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11415, d111033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11416 q = 1) (hb : d107483 q = 1) : d111034 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11416, d111034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11416, d111034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11422 q = 1) (hb : d107483 q = 1) : d11422 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11423 q = 1) (hb : d107483 q = 1) : d111038 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11423, d111038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24804 q ha hb
    | true =>
      simp only [d11423, d111038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11424 q = 1) (hb : d107483 q = 1) : d111039 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11424, d111039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11424, d111039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11425 q = 1) (hb : d107483 q = 1) : d111040 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11425, d111040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11425, d111040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11438 q = 1) (hb : d107483 q = 1) : d111049 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11438, d111049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24806 q ha hb
    | true =>
      simp only [d11438, d111049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24798 q ha hb
  have h11 (q : Pattern) (ha : d107483 q = 1) (hb : d108938 q = 1) : d111050 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108938, d111050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108938, d111050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d11477 q = 1) (hb : d107483 q = 1) : d111055 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11477, d111055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24808 q ha hb
    | true =>
      simp only [d11477, d111055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d11478 q = 1) (hb : d107483 q = 1) : d111056 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11478, d111056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d11478, d111056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d107483 q = 1) (hb : d108939 q = 1) : d111057 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108939, d111057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108939, d111057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d107483 q = 1) (hb : d108940 q = 1) : d111058 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108940, d111058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108940, d111058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107483 q = 1) (hb : d108941 q = 1) : d111059 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108941, d111059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d108941, d111059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d11484 q = 1) (hb : d107483 q = 1) : d11484 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d11485 q = 1) (hb : d107483 q = 1) : d111062 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11485, d111062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24810 q ha hb
    | true =>
      simp only [d11485, d111062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d11486 q = 1) (hb : d107483 q = 1) : d111063 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11486, d111063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11486, d111063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d11487 q = 1) (hb : d107483 q = 1) : d111064 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11487, d111064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d11487, d111064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d11488 q = 1) (hb : d107483 q = 1) : d111065 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11488, d111065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11488, d111065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d11490 q = 1) (hb : d107483 q = 1) : d11490 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d11491 q = 1) (hb : d107483 q = 1) : d111067 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11491, d111067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24811 q ha hb
    | true =>
      simp only [d11491, d111067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d11492 q = 1) (hb : d107483 q = 1) : d111068 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11492, d111068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11492, d111068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d11493 q = 1) (hb : d107483 q = 1) : d111069 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11493, d111069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d11493, d111069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d11495 q = 1) (hb : d107483 q = 1) : d111071 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11495, d111071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24812 q ha hb
    | true =>
      simp only [d11495, d111071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24800 q ha hb
  have h27 (q : Pattern) (ha : d107483 q = 1) (hb : d108943 q = 1) : d111072 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108943, d111072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
    | true =>
      simp only [d108943, d111072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d11501 q = 1) (hb : d107483 q = 1) : d111074 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11501, d111074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24813 q ha hb
    | true =>
      simp only [d11501, d111074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d11502 q = 1) (hb : d107483 q = 1) : d111075 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11502, d111075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d11502, d111075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d107483 q = 1) (hb : d108944 q = 1) : d111076 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108944, d111076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d108944, d111076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d107483 q = 1) (hb : d108945 q = 1) : d111077 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108945, d111077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d108945, d111077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d107483 q = 1) (hb : d108946 q = 1) : d111078 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108946, d111078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d108946, d111078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d107483 q = 1) (hb : d108947 q = 1) : d111079 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108947, d111079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108947, d111079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro24815 (p : Pattern) (ha : d107483 p = 1) (hb : d108954 p = 1) : d111088 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11495 q = 1) (hb : d107483 q = 1) : d111071 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11495, d111071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24812 q ha hb
    | true =>
      simp only [d11495, d111071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24800 q ha hb
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d108943 q = 1) : d111072 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108943, d111072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108943, d111072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d11501 q = 1) (hb : d107483 q = 1) : d111074 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11501, d111074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24813 q ha hb
    | true =>
      simp only [d11501, d111074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11502 q = 1) (hb : d107483 q = 1) : d111075 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11502, d111075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11502, d111075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d108944 q = 1) : d111076 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108944, d111076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108944, d111076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d108952 q = 1) : d111086 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108952, d111086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108952, d111086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107483 q = 1) (hb : d108953 q = 1) : d111087 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108953, d111087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108953, d111087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107483 q = 1) (hb : d108954 q = 1) : d111088 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108954, d111088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108954, d111088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24816 (p : Pattern) (ha : d11546 p = 1) (hb : d107483 p = 1) : d111095 p = 1 := by
  have h0 (q : Pattern) (ha : d11540 q = 1) (hb : d85721 q = 1) : d11540 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11544 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11545 q = 1) (hb : d107483 q = 1) : d111094 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11545, d107483, d111094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11545, d107483, d111094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11546 q = 1) (hb : d107483 q = 1) : d111095 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11546, d111095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11546, d111095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro24817 (p : Pattern) (ha : d11551 p = 1) (hb : d107483 p = 1) : d111099 p = 1 := by
  have h0 (q : Pattern) (ha : d11544 q = 1) (hb : d85721 q = 1) : d11544 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11549 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11550 q = 1) (hb : d107483 q = 1) : d111098 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11550, d107483, d111098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11550, d107483, d111098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11551 q = 1) (hb : d107483 q = 1) : d111099 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11551, d111099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11551, d111099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro24818 (p : Pattern) (ha : d11557 p = 1) (hb : d107483 p = 1) : d111105 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11547 q = 1) (hb : d107483 q = 1) : d111096 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11547, d111096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24816 q ha hb
    | true =>
      simp only [d11547, d111096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11548 q = 1) (hb : d107483 q = 1) : d111097 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11548, d111097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11548, d111097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11552 q = 1) (hb : d107483 q = 1) : d111100 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11552, d111100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24817 q ha hb
    | true =>
      simp only [d11552, d111100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11553 q = 1) (hb : d107483 q = 1) : d111101 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11553, d111101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11553, d111101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11554 q = 1) (hb : d107483 q = 1) : d111102 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11554, d111102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11554, d111102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11555 q = 1) (hb : d107483 q = 1) : d111103 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11555, d111103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11555, d111103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11556 q = 1) (hb : d107483 q = 1) : d111104 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11556, d111104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11556, d111104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11557 q = 1) (hb : d107483 q = 1) : d111105 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11557, d111105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11557, d111105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24819 (p : Pattern) (ha : d11565 p = 1) (hb : d107483 p = 1) : d111109 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11552 q = 1) (hb : d107483 q = 1) : d111100 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11552, d111100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24817 q ha hb
    | true =>
      simp only [d11552, d111100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11553 q = 1) (hb : d107483 q = 1) : d111101 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11553, d111101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11553, d111101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11561 q = 1) (hb : d107483 q = 1) : d11561 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11562 q = 1) (hb : d107483 q = 1) : d111106 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11562, d111106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11562, d111106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11563 q = 1) (hb : d107483 q = 1) : d111107 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11563, d111107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11563, d111107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11564 q = 1) (hb : d107483 q = 1) : d111108 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11564, d111108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11564, d111108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11565 q = 1) (hb : d107483 q = 1) : d111109 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11565, d111109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11565, d111109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro24820 (p : Pattern) (ha : d11598 p = 1) (hb : d107483 p = 1) : d111099 p = 1 := by
  have h0 (q : Pattern) (ha : d11544 q = 1) (hb : d85721 q = 1) : d11544 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11596 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11597 q = 1) (hb : d107483 q = 1) : d111098 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11597, d107483, d111098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11597, d107483, d111098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11598 q = 1) (hb : d107483 q = 1) : d111099 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11598, d111099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11598, d111099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro24821 (p : Pattern) (ha : d11604 p = 1) (hb : d107483 p = 1) : d111115 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11599 q = 1) (hb : d107483 q = 1) : d111100 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11599, d111100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24820 q ha hb
    | true =>
      simp only [d11599, d111100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11600 q = 1) (hb : d107483 q = 1) : d111101 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11600, d111101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11600, d111101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11601 q = 1) (hb : d107483 q = 1) : d111112 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11601, d111112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11601, d111112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11602 q = 1) (hb : d107483 q = 1) : d111113 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11602, d111113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11602, d111113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11603 q = 1) (hb : d107483 q = 1) : d111114 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11603, d111114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11603, d111114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11604 q = 1) (hb : d107483 q = 1) : d111115 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11604, d111115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11604, d111115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24822 (p : Pattern) (ha : d107483 p = 1) (hb : d108964 p = 1) : d111121 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11566 q = 1) (hb : d107483 q = 1) : d111110 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11566, d111110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24818 q ha hb
    | true =>
      simp only [d11566, d111110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24819 q ha hb
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d108960 q = 1) : d111111 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108960, d111111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108960, d111111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d11605 q = 1) (hb : d107483 q = 1) : d111116 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11605, d111116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24821 q ha hb
    | true =>
      simp only [d11605, d111116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11606 q = 1) (hb : d107483 q = 1) : d111117 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11606, d111117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11606, d111117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d108961 q = 1) : d111118 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108961, d111118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108961, d111118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d108962 q = 1) : d111119 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108962, d111119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108962, d111119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107483 q = 1) (hb : d108963 q = 1) : d111120 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108963, d111120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108963, d111120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107483 q = 1) (hb : d108964 q = 1) : d111121 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108964, d111121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108964, d111121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24823 (p : Pattern) (ha : d107483 p = 1) (hb : d108970 p = 1) : d111127 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11396 q = 1) (hb : d107483 q = 1) : d111017 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11396, d111017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11396, d111017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24799 q ha hb
  have h2 (q : Pattern) (ha : d11397 q = 1) (hb : d107483 q = 1) : d111018 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11397, d111018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11397, d111018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11406 q = 1) (hb : d107483 q = 1) : d111026 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11406, d111026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24799 q ha hb
    | true =>
      simp only [d11406, d111026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24801 q ha hb
  have h4 (q : Pattern) (ha : d11407 q = 1) (hb : d107483 q = 1) : d111027 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11407, d111027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11407, d111027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11408 q = 1) (hb : d107483 q = 1) : d111028 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11408, d111028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11408, d111028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d108948 q = 1) : d111080 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108948, d111080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24809 q ha hb
    | true =>
      simp only [d108948, d111080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24814 q ha hb
  have h7 (q : Pattern) (ha : d11519 q = 1) (hb : d107483 q = 1) : d11519 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d11520 q = 1) (hb : d107483 q = 1) : d111082 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11520, d111082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24802 q ha hb
    | true =>
      simp only [d11520, d111082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107483 q = 1) (hb : d108949 q = 1) : d111083 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108949, d111083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108949, d111083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d107483 q = 1) (hb : d108950 q = 1) : d111084 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108950, d111084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108950, d111084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d107483 q = 1) (hb : d108951 q = 1) : d111085 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108951, d111085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d108951, d111085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d107483 q = 1) (hb : d108955 q = 1) : d111089 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108955, d111089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108955, d111089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24815 q ha hb
  have h13 (q : Pattern) (ha : d11529 q = 1) (hb : d107483 q = 1) : d11529 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d107483 q = 1) (hb : d108956 q = 1) : d111090 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108956, d111090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108956, d111090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d107483 q = 1) (hb : d108957 q = 1) : d111091 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108957, d111091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108957, d111091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d107483 q = 1) (hb : d108958 q = 1) : d111092 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108958, d111092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108958, d111092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d107483 q = 1) (hb : d108959 q = 1) : d111093 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108959, d111093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108959, d111093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d107483 q = 1) (hb : d108965 q = 1) : d111122 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108965, d111122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108965, d111122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24822 q ha hb
  have h19 (q : Pattern) (ha : d11622 q = 1) (hb : d107483 q = 1) : d11622 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d107483 q = 1) (hb : d108966 q = 1) : d111123 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108966, d111123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d108966, d111123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d107483 q = 1) (hb : d108967 q = 1) : d111124 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108967, d111124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d108967, d111124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d107483 q = 1) (hb : d108968 q = 1) : d111125 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108968, d111125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108968, d111125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d107483 q = 1) (hb : d108969 q = 1) : d111126 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108969, d111126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d108969, d111126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d107483 q = 1) (hb : d108970 q = 1) : d111127 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108970, d111127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108970, d111127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro24824 (p : Pattern) (ha : d107483 p = 1) (hb : d108976 p = 1) : d111133 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107483 q = 1) (hb : d108971 q = 1) : d111128 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108971, d111128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108971, d111128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24823 q ha hb
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d108972 q = 1) : d111129 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108972, d111129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108972, d111129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d108973 q = 1) : d111130 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108973, d111130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108973, d111130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d108974 q = 1) : d111131 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108974, d111131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108974, d111131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d108975 q = 1) : d111132 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108975, d111132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108975, d111132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d108976 q = 1) : d111133 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108976, d111133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108976, d111133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24825 (p : Pattern) (ha : d11646 p = 1) (hb : d107483 p = 1) : d111138 p = 1 := by
  have h0 (q : Pattern) (ha : d11643 q = 1) (hb : d85721 q = 1) : d11643 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11644 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11645 q = 1) (hb : d107483 q = 1) : d111137 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11645, d107483, d111137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11645, d107483, d111137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11646 q = 1) (hb : d107483 q = 1) : d111138 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11646, d111138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11646, d111138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro24826 (p : Pattern) (ha : d11656 p = 1) (hb : d107483 p = 1) : d111144 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11647 q = 1) (hb : d107483 q = 1) : d111139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24825 q ha hb
    | true =>
      simp only [d11647, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11648 q = 1) (hb : d107483 q = 1) : d111140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11652 q = 1) (hb : d107483 q = 1) : d11652 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11653 q = 1) (hb : d107483 q = 1) : d111141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11653, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11654 q = 1) (hb : d107483 q = 1) : d111142 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11654, d111142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11654, d111142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11655 q = 1) (hb : d107483 q = 1) : d111143 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11655, d111143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11655, d111143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11656 q = 1) (hb : d107483 q = 1) : d111144 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11656, d111144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11656, d111144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24827 (p : Pattern) (ha : d11666 p = 1) (hb : d107483 p = 1) : d111150 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11660 q = 1) (hb : d107483 q = 1) : d11660 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11661 q = 1) (hb : d107483 q = 1) : d111145 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11661, d111145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24826 q ha hb
    | true =>
      simp only [d11661, d111145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11662 q = 1) (hb : d107483 q = 1) : d111146 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11662, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11662, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11663 q = 1) (hb : d107483 q = 1) : d111147 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11663, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11663, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11664 q = 1) (hb : d107483 q = 1) : d111148 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11664, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11664, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11665 q = 1) (hb : d107483 q = 1) : d111149 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11665, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11665, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11666 q = 1) (hb : d107483 q = 1) : d111150 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11666, d111150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11666, d111150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24828 (p : Pattern) (ha : d11669 p = 1) (hb : d107483 p = 1) : d111153 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11647 q = 1) (hb : d107483 q = 1) : d111139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24825 q ha hb
    | true =>
      simp only [d11647, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11648 q = 1) (hb : d107483 q = 1) : d111140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11652 q = 1) (hb : d107483 q = 1) : d11652 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11653 q = 1) (hb : d107483 q = 1) : d111141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11653, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11654 q = 1) (hb : d107483 q = 1) : d111142 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11654, d111142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11654, d111142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11655 q = 1) (hb : d107483 q = 1) : d111143 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11655, d111143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11655, d111143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11669 q = 1) (hb : d107483 q = 1) : d111153 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11669, d111153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11669, d111153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro24829 (p : Pattern) (ha : d11676 p = 1) (hb : d107483 p = 1) : d111159 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11660 q = 1) (hb : d107483 q = 1) : d11660 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11661 q = 1) (hb : d107483 q = 1) : d111145 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11661, d111145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24826 q ha hb
    | true =>
      simp only [d11661, d111145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11662 q = 1) (hb : d107483 q = 1) : d111146 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11662, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11662, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11663 q = 1) (hb : d107483 q = 1) : d111147 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11663, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11663, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11664 q = 1) (hb : d107483 q = 1) : d111148 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11664, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11664, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11665 q = 1) (hb : d107483 q = 1) : d111149 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11665, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11665, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11670 q = 1) (hb : d107483 q = 1) : d11670 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d11671 q = 1) (hb : d107483 q = 1) : d111154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11671, d111154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24828 q ha hb
    | true =>
      simp only [d11671, d111154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11672 q = 1) (hb : d107483 q = 1) : d111155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11672, d111155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11672, d111155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11673 q = 1) (hb : d107483 q = 1) : d111156 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11673, d111156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11673, d111156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11674 q = 1) (hb : d107483 q = 1) : d111157 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11674, d111157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11674, d111157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11675 q = 1) (hb : d107483 q = 1) : d111158 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11675, d111158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11675, d111158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11676 q = 1) (hb : d107483 q = 1) : d111159 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11676, d111159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11676, d111159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro24830 (p : Pattern) (ha : d11784 p = 1) (hb : d107483 p = 1) : d111215 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11660 q = 1) (hb : d107483 q = 1) : d11660 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11661 q = 1) (hb : d107483 q = 1) : d111145 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11661, d111145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24826 q ha hb
    | true =>
      simp only [d11661, d111145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11662 q = 1) (hb : d107483 q = 1) : d111146 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11662, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11662, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11663 q = 1) (hb : d107483 q = 1) : d111147 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11663, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11663, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11664 q = 1) (hb : d107483 q = 1) : d111148 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11664, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11664, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11665 q = 1) (hb : d107483 q = 1) : d111149 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11665, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11665, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11783 q = 1) (hb : d107483 q = 1) : d11783 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d11784 q = 1) (hb : d107483 q = 1) : d111215 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11784, d111215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11784, d111215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24831 (p : Pattern) (ha : d11681 p = 1) (hb : d107483 p = 1) : d111164 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11647 q = 1) (hb : d107483 q = 1) : d111139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24825 q ha hb
    | true =>
      simp only [d11647, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11648 q = 1) (hb : d107483 q = 1) : d111140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11652 q = 1) (hb : d107483 q = 1) : d11652 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11653 q = 1) (hb : d107483 q = 1) : d111141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11653, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11654 q = 1) (hb : d107483 q = 1) : d111142 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11654, d111142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11654, d111142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11680 q = 1) (hb : d107483 q = 1) : d111163 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11680, d111163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11680, d111163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11681 q = 1) (hb : d107483 q = 1) : d111164 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11681, d111164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11681, d111164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24832 (p : Pattern) (ha : d11690 p = 1) (hb : d107483 p = 1) : d111171 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11647 q = 1) (hb : d107483 q = 1) : d111139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24825 q ha hb
    | true =>
      simp only [d11647, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11648 q = 1) (hb : d107483 q = 1) : d111140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11652 q = 1) (hb : d107483 q = 1) : d11652 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11653 q = 1) (hb : d107483 q = 1) : d111141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11653, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11688 q = 1) (hb : d107483 q = 1) : d111169 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11688, d111169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11688, d111169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11689 q = 1) (hb : d107483 q = 1) : d111170 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11689, d111170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11689, d111170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11690 q = 1) (hb : d107483 q = 1) : d111171 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11690, d111171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11690, d111171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24833 (p : Pattern) (ha : d11702 p = 1) (hb : d107483 p = 1) : d111176 p = 1 := by
  have h0 (q : Pattern) (ha : d11700 q = 1) (hb : d85721 q = 1) : d11700 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11643 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11701 q = 1) (hb : d107483 q = 1) : d111175 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11701, d107483, d111175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11701, d107483, d111175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11702 q = 1) (hb : d107483 q = 1) : d111176 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11702, d111176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11702, d111176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro24834 (p : Pattern) (ha : d11708 p = 1) (hb : d107483 p = 1) : d111182 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11703 q = 1) (hb : d107483 q = 1) : d111177 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11703, d111177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24833 q ha hb
    | true =>
      simp only [d11703, d111177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11704 q = 1) (hb : d107483 q = 1) : d111178 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11704, d111178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11704, d111178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11647 q = 1) (hb : d107483 q = 1) : d111139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24825 q ha hb
    | true =>
      simp only [d11647, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11648 q = 1) (hb : d107483 q = 1) : d111140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11705 q = 1) (hb : d107483 q = 1) : d111179 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11705, d111179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11705, d111179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11706 q = 1) (hb : d107483 q = 1) : d111180 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11706, d111180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11706, d111180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11707 q = 1) (hb : d107483 q = 1) : d111181 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11707, d111181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11707, d111181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11708 q = 1) (hb : d107483 q = 1) : d111182 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11708, d111182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11708, d111182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24835 (p : Pattern) (ha : d11741 p = 1) (hb : d107483 p = 1) : d111138 p = 1 := by
  have h0 (q : Pattern) (ha : d11643 q = 1) (hb : d85721 q = 1) : d11643 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11739 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11740 q = 1) (hb : d107483 q = 1) : d111137 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11740, d107483, d111137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11740, d107483, d111137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11741 q = 1) (hb : d107483 q = 1) : d111138 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11741, d111138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11741, d111138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro24836 (p : Pattern) (ha : d11747 p = 1) (hb : d107483 p = 1) : d111188 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11742 q = 1) (hb : d107483 q = 1) : d111139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11742, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24835 q ha hb
    | true =>
      simp only [d11742, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11743 q = 1) (hb : d107483 q = 1) : d111140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11743, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11743, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11744 q = 1) (hb : d107483 q = 1) : d111185 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11744, d111185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11744, d111185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11745 q = 1) (hb : d107483 q = 1) : d111186 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11745, d111186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11745, d111186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11746 q = 1) (hb : d107483 q = 1) : d111187 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11746, d111187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11746, d111187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11747 q = 1) (hb : d107483 q = 1) : d111188 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11747, d111188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11747, d111188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24837 (p : Pattern) (ha : d107483 p = 1) (hb : d108984 p = 1) : d111194 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11683 q = 1) (hb : d107483 q = 1) : d11683 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11684 q = 1) (hb : d107483 q = 1) : d111165 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11684, d111165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24831 q ha hb
    | true =>
      simp only [d11684, d111165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11685 q = 1) (hb : d107483 q = 1) : d111166 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11685, d111166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11685, d111166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11686 q = 1) (hb : d107483 q = 1) : d111167 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11686, d111167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11686, d111167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11687 q = 1) (hb : d107483 q = 1) : d111168 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11687, d111168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11687, d111168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11693 q = 1) (hb : d107483 q = 1) : d11693 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11694 q = 1) (hb : d107483 q = 1) : d111172 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11694, d111172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24832 q ha hb
    | true =>
      simp only [d11694, d111172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11695 q = 1) (hb : d107483 q = 1) : d111173 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11695, d111173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11695, d111173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11696 q = 1) (hb : d107483 q = 1) : d111174 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11696, d111174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11696, d111174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11709 q = 1) (hb : d107483 q = 1) : d111183 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11709, d111183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24834 q ha hb
    | true =>
      simp only [d11709, d111183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24826 q ha hb
  have h11 (q : Pattern) (ha : d107483 q = 1) (hb : d108980 q = 1) : d111184 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108980, d111184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108980, d111184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d11748 q = 1) (hb : d107483 q = 1) : d111189 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11748, d111189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24836 q ha hb
    | true =>
      simp only [d11748, d111189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d11749 q = 1) (hb : d107483 q = 1) : d111190 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11749, d111190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d11749, d111190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d107483 q = 1) (hb : d108981 q = 1) : d111191 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108981, d111191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108981, d111191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d107483 q = 1) (hb : d108982 q = 1) : d111192 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108982, d111192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108982, d111192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107483 q = 1) (hb : d108983 q = 1) : d111193 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108983, d111193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d108983, d111193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d107483 q = 1) (hb : d108984 q = 1) : d111194 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108984, d111194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108984, d111194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro24838 (p : Pattern) (ha : d11754 p = 1) (hb : d107483 p = 1) : d111195 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11647 q = 1) (hb : d107483 q = 1) : d111139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24825 q ha hb
    | true =>
      simp only [d11647, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11648 q = 1) (hb : d107483 q = 1) : d111140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11652 q = 1) (hb : d107483 q = 1) : d11652 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11653 q = 1) (hb : d107483 q = 1) : d111141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11653, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11654 q = 1) (hb : d107483 q = 1) : d111142 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11654, d111142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11654, d111142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11680 q = 1) (hb : d107483 q = 1) : d111163 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11680, d111163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11680, d111163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11754 q = 1) (hb : d107483 q = 1) : d111195 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11754, d111195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11754, d111195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro24839 (p : Pattern) (ha : d11760 p = 1) (hb : d107483 p = 1) : d111200 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11647 q = 1) (hb : d107483 q = 1) : d111139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24825 q ha hb
    | true =>
      simp only [d11647, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11648 q = 1) (hb : d107483 q = 1) : d111140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11652 q = 1) (hb : d107483 q = 1) : d11652 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11653 q = 1) (hb : d107483 q = 1) : d111141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11653, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11688 q = 1) (hb : d107483 q = 1) : d111169 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11688, d111169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11688, d111169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11689 q = 1) (hb : d107483 q = 1) : d111170 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11689, d111170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11689, d111170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11760 q = 1) (hb : d107483 q = 1) : d111200 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11760, d111200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11760, d111200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro24840 (p : Pattern) (ha : d11765 p = 1) (hb : d107483 p = 1) : d111204 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11703 q = 1) (hb : d107483 q = 1) : d111177 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11703, d111177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24833 q ha hb
    | true =>
      simp only [d11703, d111177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11704 q = 1) (hb : d107483 q = 1) : d111178 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11704, d111178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11704, d111178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11647 q = 1) (hb : d107483 q = 1) : d111139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24825 q ha hb
    | true =>
      simp only [d11647, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11648 q = 1) (hb : d107483 q = 1) : d111140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11705 q = 1) (hb : d107483 q = 1) : d111179 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11705, d111179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11705, d111179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11706 q = 1) (hb : d107483 q = 1) : d111180 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11706, d111180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11706, d111180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11707 q = 1) (hb : d107483 q = 1) : d111181 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11707, d111181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11707, d111181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11765 q = 1) (hb : d107483 q = 1) : d111204 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11765, d111204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11765, d111204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24841 (p : Pattern) (ha : d11771 p = 1) (hb : d107483 p = 1) : d111207 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11742 q = 1) (hb : d107483 q = 1) : d111139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11742, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24835 q ha hb
    | true =>
      simp only [d11742, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11743 q = 1) (hb : d107483 q = 1) : d111140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11743, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11743, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11744 q = 1) (hb : d107483 q = 1) : d111185 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11744, d111185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11744, d111185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11745 q = 1) (hb : d107483 q = 1) : d111186 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11745, d111186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11745, d111186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11746 q = 1) (hb : d107483 q = 1) : d111187 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11746, d111187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11746, d111187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11771 q = 1) (hb : d107483 q = 1) : d111207 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11771, d111207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11771, d111207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24842 (p : Pattern) (ha : d107483 p = 1) (hb : d108989 p = 1) : d111213 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11683 q = 1) (hb : d107483 q = 1) : d11683 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11684 q = 1) (hb : d107483 q = 1) : d111165 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11684, d111165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24831 q ha hb
    | true =>
      simp only [d11684, d111165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11685 q = 1) (hb : d107483 q = 1) : d111166 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11685, d111166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11685, d111166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11686 q = 1) (hb : d107483 q = 1) : d111167 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11686, d111167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11686, d111167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11687 q = 1) (hb : d107483 q = 1) : d111168 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11687, d111168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11687, d111168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11693 q = 1) (hb : d107483 q = 1) : d11693 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11694 q = 1) (hb : d107483 q = 1) : d111172 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11694, d111172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24832 q ha hb
    | true =>
      simp only [d11694, d111172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11695 q = 1) (hb : d107483 q = 1) : d111173 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11695, d111173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11695, d111173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11696 q = 1) (hb : d107483 q = 1) : d111174 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11696, d111174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11696, d111174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11709 q = 1) (hb : d107483 q = 1) : d111183 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11709, d111183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24834 q ha hb
    | true =>
      simp only [d11709, d111183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24826 q ha hb
  have h11 (q : Pattern) (ha : d107483 q = 1) (hb : d108980 q = 1) : d111184 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108980, d111184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108980, d111184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d11748 q = 1) (hb : d107483 q = 1) : d111189 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11748, d111189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24836 q ha hb
    | true =>
      simp only [d11748, d111189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d11749 q = 1) (hb : d107483 q = 1) : d111190 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11749, d111190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d11749, d111190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d107483 q = 1) (hb : d108981 q = 1) : d111191 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108981, d111191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108981, d111191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d107483 q = 1) (hb : d108982 q = 1) : d111192 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108982, d111192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108982, d111192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107483 q = 1) (hb : d108983 q = 1) : d111193 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108983, d111193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d108983, d111193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d11755 q = 1) (hb : d107483 q = 1) : d11755 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d11756 q = 1) (hb : d107483 q = 1) : d111196 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11756, d111196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24838 q ha hb
    | true =>
      simp only [d11756, d111196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d11757 q = 1) (hb : d107483 q = 1) : d111197 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11757, d111197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11757, d111197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d11758 q = 1) (hb : d107483 q = 1) : d111198 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11758, d111198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d11758, d111198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d11759 q = 1) (hb : d107483 q = 1) : d111199 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11759, d111199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11759, d111199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d11761 q = 1) (hb : d107483 q = 1) : d11761 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d11762 q = 1) (hb : d107483 q = 1) : d111201 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11762, d111201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24839 q ha hb
    | true =>
      simp only [d11762, d111201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d11763 q = 1) (hb : d107483 q = 1) : d111202 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11763, d111202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11763, d111202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d11764 q = 1) (hb : d107483 q = 1) : d111203 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11764, d111203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d11764, d111203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d11766 q = 1) (hb : d107483 q = 1) : d111205 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11766, d111205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24840 q ha hb
    | true =>
      simp only [d11766, d111205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24828 q ha hb
  have h27 (q : Pattern) (ha : d107483 q = 1) (hb : d108985 q = 1) : d111206 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108985, d111206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
    | true =>
      simp only [d108985, d111206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d11772 q = 1) (hb : d107483 q = 1) : d111208 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11772, d111208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24841 q ha hb
    | true =>
      simp only [d11772, d111208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d11773 q = 1) (hb : d107483 q = 1) : d111209 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11773, d111209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d11773, d111209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d107483 q = 1) (hb : d108986 q = 1) : d111210 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108986, d111210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d108986, d111210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d107483 q = 1) (hb : d108987 q = 1) : d111211 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108987, d111211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d108987, d111211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d107483 q = 1) (hb : d108988 q = 1) : d111212 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108988, d111212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d108988, d111212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d107483 q = 1) (hb : d108989 q = 1) : d111213 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108989, d111213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108989, d111213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro24843 (p : Pattern) (ha : d107483 p = 1) (hb : d108996 p = 1) : d111222 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11766 q = 1) (hb : d107483 q = 1) : d111205 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11766, d111205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24840 q ha hb
    | true =>
      simp only [d11766, d111205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24828 q ha hb
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d108985 q = 1) : d111206 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108985, d111206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108985, d111206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d11772 q = 1) (hb : d107483 q = 1) : d111208 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11772, d111208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24841 q ha hb
    | true =>
      simp only [d11772, d111208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11773 q = 1) (hb : d107483 q = 1) : d111209 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11773, d111209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11773, d111209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d108986 q = 1) : d111210 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108986, d111210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108986, d111210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d108994 q = 1) : d111220 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108994, d111220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108994, d111220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107483 q = 1) (hb : d108995 q = 1) : d111221 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108995, d111221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108995, d111221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107483 q = 1) (hb : d108996 q = 1) : d111222 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108996, d111222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108996, d111222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24844 (p : Pattern) (ha : d11817 p = 1) (hb : d107483 p = 1) : d111229 p = 1 := by
  have h0 (q : Pattern) (ha : d11811 q = 1) (hb : d85721 q = 1) : d11811 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11815 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11816 q = 1) (hb : d107483 q = 1) : d111228 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11816, d107483, d111228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11816, d107483, d111228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11817 q = 1) (hb : d107483 q = 1) : d111229 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11817, d111229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11817, d111229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro24845 (p : Pattern) (ha : d11822 p = 1) (hb : d107483 p = 1) : d111233 p = 1 := by
  have h0 (q : Pattern) (ha : d11815 q = 1) (hb : d85721 q = 1) : d11815 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11820 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11821 q = 1) (hb : d107483 q = 1) : d111232 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11821, d107483, d111232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11821, d107483, d111232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11822 q = 1) (hb : d107483 q = 1) : d111233 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11822, d111233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11822, d111233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro24846 (p : Pattern) (ha : d11828 p = 1) (hb : d107483 p = 1) : d111239 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11818 q = 1) (hb : d107483 q = 1) : d111230 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11818, d111230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24844 q ha hb
    | true =>
      simp only [d11818, d111230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11819 q = 1) (hb : d107483 q = 1) : d111231 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11819, d111231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11819, d111231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11823 q = 1) (hb : d107483 q = 1) : d111234 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11823, d111234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24845 q ha hb
    | true =>
      simp only [d11823, d111234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11824 q = 1) (hb : d107483 q = 1) : d111235 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11824, d111235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11824, d111235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11825 q = 1) (hb : d107483 q = 1) : d111236 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11825, d111236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11825, d111236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11826 q = 1) (hb : d107483 q = 1) : d111237 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11826, d111237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11826, d111237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11827 q = 1) (hb : d107483 q = 1) : d111238 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11827, d111238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11827, d111238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11828 q = 1) (hb : d107483 q = 1) : d111239 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11828, d111239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11828, d111239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24847 (p : Pattern) (ha : d11836 p = 1) (hb : d107483 p = 1) : d111243 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11823 q = 1) (hb : d107483 q = 1) : d111234 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11823, d111234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24845 q ha hb
    | true =>
      simp only [d11823, d111234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11824 q = 1) (hb : d107483 q = 1) : d111235 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11824, d111235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11824, d111235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11832 q = 1) (hb : d107483 q = 1) : d11832 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11833 q = 1) (hb : d107483 q = 1) : d111240 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11833, d111240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11833, d111240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11834 q = 1) (hb : d107483 q = 1) : d111241 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11834, d111241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11834, d111241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11835 q = 1) (hb : d107483 q = 1) : d111242 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11835, d111242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11835, d111242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11836 q = 1) (hb : d107483 q = 1) : d111243 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11836, d111243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11836, d111243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro24848 (p : Pattern) (ha : d11869 p = 1) (hb : d107483 p = 1) : d111233 p = 1 := by
  have h0 (q : Pattern) (ha : d11815 q = 1) (hb : d85721 q = 1) : d11815 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11867 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11868 q = 1) (hb : d107483 q = 1) : d111232 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11868, d107483, d111232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11868, d107483, d111232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11869 q = 1) (hb : d107483 q = 1) : d111233 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11869, d111233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11869, d111233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro24849 (p : Pattern) (ha : d11875 p = 1) (hb : d107483 p = 1) : d111249 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11870 q = 1) (hb : d107483 q = 1) : d111234 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11870, d111234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24848 q ha hb
    | true =>
      simp only [d11870, d111234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11871 q = 1) (hb : d107483 q = 1) : d111235 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11871, d111235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11871, d111235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11872 q = 1) (hb : d107483 q = 1) : d111246 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11872, d111246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11872, d111246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11873 q = 1) (hb : d107483 q = 1) : d111247 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11873, d111247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11873, d111247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11874 q = 1) (hb : d107483 q = 1) : d111248 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11874, d111248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11874, d111248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11875 q = 1) (hb : d107483 q = 1) : d111249 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11875, d111249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11875, d111249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24850 (p : Pattern) (ha : d107483 p = 1) (hb : d109006 p = 1) : d111255 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11837 q = 1) (hb : d107483 q = 1) : d111244 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11837, d111244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24846 q ha hb
    | true =>
      simp only [d11837, d111244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24847 q ha hb
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d109002 q = 1) : d111245 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109002, d111245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109002, d111245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d11876 q = 1) (hb : d107483 q = 1) : d111250 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11876, d111250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24849 q ha hb
    | true =>
      simp only [d11876, d111250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11877 q = 1) (hb : d107483 q = 1) : d111251 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11877, d111251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11877, d111251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d109003 q = 1) : d111252 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109003, d111252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109003, d111252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d109004 q = 1) : d111253 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109004, d111253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109004, d111253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107483 q = 1) (hb : d109005 q = 1) : d111254 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109005, d111254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109005, d111254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107483 q = 1) (hb : d109006 q = 1) : d111255 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109006, d111255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109006, d111255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24851 (p : Pattern) (ha : d107483 p = 1) (hb : d109012 p = 1) : d111261 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11667 q = 1) (hb : d107483 q = 1) : d111151 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11667, d111151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11667, d111151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24827 q ha hb
  have h2 (q : Pattern) (ha : d11668 q = 1) (hb : d107483 q = 1) : d111152 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11668, d111152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11668, d111152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11677 q = 1) (hb : d107483 q = 1) : d111160 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11677, d111160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24827 q ha hb
    | true =>
      simp only [d11677, d111160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24829 q ha hb
  have h4 (q : Pattern) (ha : d11678 q = 1) (hb : d107483 q = 1) : d111161 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11678, d111161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11678, d111161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11679 q = 1) (hb : d107483 q = 1) : d111162 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11679, d111162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11679, d111162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d108990 q = 1) : d111214 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108990, d111214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24837 q ha hb
    | true =>
      simp only [d108990, d111214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24842 q ha hb
  have h7 (q : Pattern) (ha : d11790 q = 1) (hb : d107483 q = 1) : d11790 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d11791 q = 1) (hb : d107483 q = 1) : d111216 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11791, d111216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24830 q ha hb
    | true =>
      simp only [d11791, d111216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107483 q = 1) (hb : d108991 q = 1) : d111217 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108991, d111217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108991, d111217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d107483 q = 1) (hb : d108992 q = 1) : d111218 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108992, d111218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108992, d111218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d107483 q = 1) (hb : d108993 q = 1) : d111219 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108993, d111219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d108993, d111219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d107483 q = 1) (hb : d108997 q = 1) : d111223 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108997, d111223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108997, d111223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24843 q ha hb
  have h13 (q : Pattern) (ha : d11800 q = 1) (hb : d107483 q = 1) : d11800 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d107483 q = 1) (hb : d108998 q = 1) : d111224 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108998, d111224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108998, d111224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d107483 q = 1) (hb : d108999 q = 1) : d111225 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108999, d111225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108999, d111225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d107483 q = 1) (hb : d109000 q = 1) : d111226 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109000, d111226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d109000, d111226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d107483 q = 1) (hb : d109001 q = 1) : d111227 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109001, d111227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109001, d111227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d107483 q = 1) (hb : d109007 q = 1) : d111256 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109007, d111256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109007, d111256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24850 q ha hb
  have h19 (q : Pattern) (ha : d11893 q = 1) (hb : d107483 q = 1) : d11893 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d107483 q = 1) (hb : d109008 q = 1) : d111257 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109008, d111257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d109008, d111257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d107483 q = 1) (hb : d109009 q = 1) : d111258 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109009, d111258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d109009, d111258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d107483 q = 1) (hb : d109010 q = 1) : d111259 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109010, d111259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d109010, d111259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d107483 q = 1) (hb : d109011 q = 1) : d111260 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109011, d111260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d109011, d111260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d107483 q = 1) (hb : d109012 q = 1) : d111261 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109012, d111261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d109012, d111261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro24852 (p : Pattern) (ha : d107483 p = 1) (hb : d109018 p = 1) : d111267 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107483 q = 1) (hb : d109013 q = 1) : d111262 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109013, d111262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109013, d111262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24851 q ha hb
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d109014 q = 1) : d111263 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109014, d111263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109014, d111263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d109015 q = 1) : d111264 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109015, d111264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109015, d111264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d109016 q = 1) : d111265 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109016, d111265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109016, d111265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d109017 q = 1) : d111266 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109017, d111266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109017, d111266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d109018 q = 1) : d111267 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109018, d111267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109018, d111267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24853 (p : Pattern) (ha : d11918 p = 1) (hb : d107483 p = 1) : d111273 p = 1 := by
  have h0 (q : Pattern) (ha : d11915 q = 1) (hb : d85721 q = 1) : d11915 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11916 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11917 q = 1) (hb : d107483 q = 1) : d111272 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11917, d107483, d111272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11917, d107483, d111272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11918 q = 1) (hb : d107483 q = 1) : d111273 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11918, d111273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11918, d111273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro24854 (p : Pattern) (ha : d11928 p = 1) (hb : d107483 p = 1) : d111279 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11919 q = 1) (hb : d107483 q = 1) : d111274 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24853 q ha hb
    | true =>
      simp only [d11919, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11920 q = 1) (hb : d107483 q = 1) : d111275 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11924 q = 1) (hb : d107483 q = 1) : d11924 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11925 q = 1) (hb : d107483 q = 1) : d111276 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11925, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11926 q = 1) (hb : d107483 q = 1) : d111277 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11926, d111277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11926, d111277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11927 q = 1) (hb : d107483 q = 1) : d111278 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11927, d111278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11927, d111278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11928 q = 1) (hb : d107483 q = 1) : d111279 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11928, d111279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11928, d111279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24855 (p : Pattern) (ha : d11938 p = 1) (hb : d107483 p = 1) : d111285 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11932 q = 1) (hb : d107483 q = 1) : d11932 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11933 q = 1) (hb : d107483 q = 1) : d111280 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11933, d111280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24854 q ha hb
    | true =>
      simp only [d11933, d111280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11934 q = 1) (hb : d107483 q = 1) : d111281 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11934, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11934, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11935 q = 1) (hb : d107483 q = 1) : d111282 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11935, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11935, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11936 q = 1) (hb : d107483 q = 1) : d111283 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11936, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11936, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11937 q = 1) (hb : d107483 q = 1) : d111284 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11937, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11937, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11938 q = 1) (hb : d107483 q = 1) : d111285 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11938, d111285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11938, d111285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24856 (p : Pattern) (ha : d11941 p = 1) (hb : d107483 p = 1) : d111288 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11919 q = 1) (hb : d107483 q = 1) : d111274 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24853 q ha hb
    | true =>
      simp only [d11919, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11920 q = 1) (hb : d107483 q = 1) : d111275 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11924 q = 1) (hb : d107483 q = 1) : d11924 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11925 q = 1) (hb : d107483 q = 1) : d111276 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11925, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11926 q = 1) (hb : d107483 q = 1) : d111277 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11926, d111277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11926, d111277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11927 q = 1) (hb : d107483 q = 1) : d111278 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11927, d111278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11927, d111278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11941 q = 1) (hb : d107483 q = 1) : d111288 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11941, d111288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11941, d111288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro24857 (p : Pattern) (ha : d11948 p = 1) (hb : d107483 p = 1) : d111294 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11932 q = 1) (hb : d107483 q = 1) : d11932 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11933 q = 1) (hb : d107483 q = 1) : d111280 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11933, d111280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24854 q ha hb
    | true =>
      simp only [d11933, d111280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11934 q = 1) (hb : d107483 q = 1) : d111281 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11934, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11934, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11935 q = 1) (hb : d107483 q = 1) : d111282 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11935, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11935, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11936 q = 1) (hb : d107483 q = 1) : d111283 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11936, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11936, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11937 q = 1) (hb : d107483 q = 1) : d111284 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11937, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11937, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11942 q = 1) (hb : d107483 q = 1) : d11942 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d11943 q = 1) (hb : d107483 q = 1) : d111289 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11943, d111289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24856 q ha hb
    | true =>
      simp only [d11943, d111289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11944 q = 1) (hb : d107483 q = 1) : d111290 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11944, d111290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11944, d111290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11945 q = 1) (hb : d107483 q = 1) : d111291 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11945, d111291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11945, d111291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11946 q = 1) (hb : d107483 q = 1) : d111292 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11946, d111292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11946, d111292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11947 q = 1) (hb : d107483 q = 1) : d111293 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11947, d111293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11947, d111293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11948 q = 1) (hb : d107483 q = 1) : d111294 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11948, d111294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11948, d111294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro24858 (p : Pattern) (ha : d12056 p = 1) (hb : d107483 p = 1) : d111350 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11932 q = 1) (hb : d107483 q = 1) : d11932 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11933 q = 1) (hb : d107483 q = 1) : d111280 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11933, d111280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24854 q ha hb
    | true =>
      simp only [d11933, d111280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11934 q = 1) (hb : d107483 q = 1) : d111281 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11934, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11934, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11935 q = 1) (hb : d107483 q = 1) : d111282 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11935, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11935, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11936 q = 1) (hb : d107483 q = 1) : d111283 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11936, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11936, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11937 q = 1) (hb : d107483 q = 1) : d111284 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11937, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11937, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12055 q = 1) (hb : d107483 q = 1) : d12055 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12056 q = 1) (hb : d107483 q = 1) : d111350 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12056, d111350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12056, d111350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24859 (p : Pattern) (ha : d11953 p = 1) (hb : d107483 p = 1) : d111299 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11919 q = 1) (hb : d107483 q = 1) : d111274 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24853 q ha hb
    | true =>
      simp only [d11919, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11920 q = 1) (hb : d107483 q = 1) : d111275 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11924 q = 1) (hb : d107483 q = 1) : d11924 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11925 q = 1) (hb : d107483 q = 1) : d111276 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11925, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11926 q = 1) (hb : d107483 q = 1) : d111277 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11926, d111277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11926, d111277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11952 q = 1) (hb : d107483 q = 1) : d111298 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11952, d111298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11952, d111298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11953 q = 1) (hb : d107483 q = 1) : d111299 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11953, d111299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11953, d111299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24860 (p : Pattern) (ha : d11962 p = 1) (hb : d107483 p = 1) : d111306 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11919 q = 1) (hb : d107483 q = 1) : d111274 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24853 q ha hb
    | true =>
      simp only [d11919, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11920 q = 1) (hb : d107483 q = 1) : d111275 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11924 q = 1) (hb : d107483 q = 1) : d11924 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11925 q = 1) (hb : d107483 q = 1) : d111276 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11925, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11960 q = 1) (hb : d107483 q = 1) : d111304 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11960, d111304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11960, d111304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11961 q = 1) (hb : d107483 q = 1) : d111305 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11961, d111305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11961, d111305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11962 q = 1) (hb : d107483 q = 1) : d111306 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11962, d111306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11962, d111306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24861 (p : Pattern) (ha : d11974 p = 1) (hb : d107483 p = 1) : d111311 p = 1 := by
  have h0 (q : Pattern) (ha : d11972 q = 1) (hb : d85721 q = 1) : d11972 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11915 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11973 q = 1) (hb : d107483 q = 1) : d111310 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11973, d107483, d111310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11973, d107483, d111310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11974 q = 1) (hb : d107483 q = 1) : d111311 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11974, d111311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11974, d111311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro24862 (p : Pattern) (ha : d11980 p = 1) (hb : d107483 p = 1) : d111317 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11975 q = 1) (hb : d107483 q = 1) : d111312 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11975, d111312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24861 q ha hb
    | true =>
      simp only [d11975, d111312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11976 q = 1) (hb : d107483 q = 1) : d111313 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11976, d111313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11976, d111313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11919 q = 1) (hb : d107483 q = 1) : d111274 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24853 q ha hb
    | true =>
      simp only [d11919, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11920 q = 1) (hb : d107483 q = 1) : d111275 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11977 q = 1) (hb : d107483 q = 1) : d111314 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11977, d111314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11977, d111314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11978 q = 1) (hb : d107483 q = 1) : d111315 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11978, d111315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11978, d111315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11979 q = 1) (hb : d107483 q = 1) : d111316 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11979, d111316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11979, d111316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11980 q = 1) (hb : d107483 q = 1) : d111317 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11980, d111317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11980, d111317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24863 (p : Pattern) (ha : d12013 p = 1) (hb : d107483 p = 1) : d111273 p = 1 := by
  have h0 (q : Pattern) (ha : d11915 q = 1) (hb : d85721 q = 1) : d11915 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12011 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12012 q = 1) (hb : d107483 q = 1) : d111272 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12012, d107483, d111272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12012, d107483, d111272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12013 q = 1) (hb : d107483 q = 1) : d111273 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12013, d111273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12013, d111273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro24864 (p : Pattern) (ha : d12019 p = 1) (hb : d107483 p = 1) : d111323 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12014 q = 1) (hb : d107483 q = 1) : d111274 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12014, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24863 q ha hb
    | true =>
      simp only [d12014, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12015 q = 1) (hb : d107483 q = 1) : d111275 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12015, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12015, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12016 q = 1) (hb : d107483 q = 1) : d111320 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12016, d111320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12016, d111320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12017 q = 1) (hb : d107483 q = 1) : d111321 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12017, d111321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12017, d111321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12018 q = 1) (hb : d107483 q = 1) : d111322 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12018, d111322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12018, d111322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12019 q = 1) (hb : d107483 q = 1) : d111323 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12019, d111323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12019, d111323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24865 (p : Pattern) (ha : d107483 p = 1) (hb : d109027 p = 1) : d111329 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11955 q = 1) (hb : d107483 q = 1) : d11955 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11956 q = 1) (hb : d107483 q = 1) : d111300 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11956, d111300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24859 q ha hb
    | true =>
      simp only [d11956, d111300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11957 q = 1) (hb : d107483 q = 1) : d111301 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11957, d111301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11957, d111301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11958 q = 1) (hb : d107483 q = 1) : d111302 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11958, d111302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11958, d111302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11959 q = 1) (hb : d107483 q = 1) : d111303 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11959, d111303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11959, d111303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11965 q = 1) (hb : d107483 q = 1) : d11965 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11966 q = 1) (hb : d107483 q = 1) : d111307 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11966, d111307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24860 q ha hb
    | true =>
      simp only [d11966, d111307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11967 q = 1) (hb : d107483 q = 1) : d111308 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11967, d111308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11967, d111308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11968 q = 1) (hb : d107483 q = 1) : d111309 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11968, d111309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11968, d111309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11981 q = 1) (hb : d107483 q = 1) : d111318 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11981, d111318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24862 q ha hb
    | true =>
      simp only [d11981, d111318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24854 q ha hb
  have h11 (q : Pattern) (ha : d107483 q = 1) (hb : d109023 q = 1) : d111319 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109023, d111319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d109023, d111319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d12020 q = 1) (hb : d107483 q = 1) : d111324 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12020, d111324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24864 q ha hb
    | true =>
      simp only [d12020, d111324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12021 q = 1) (hb : d107483 q = 1) : d111325 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12021, d111325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12021, d111325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d107483 q = 1) (hb : d109024 q = 1) : d111326 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109024, d111326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109024, d111326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d107483 q = 1) (hb : d109025 q = 1) : d111327 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109025, d111327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d109025, d111327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107483 q = 1) (hb : d109026 q = 1) : d111328 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109026, d111328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d109026, d111328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d107483 q = 1) (hb : d109027 q = 1) : d111329 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109027, d111329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109027, d111329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro24866 (p : Pattern) (ha : d12026 p = 1) (hb : d107483 p = 1) : d111330 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11919 q = 1) (hb : d107483 q = 1) : d111274 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24853 q ha hb
    | true =>
      simp only [d11919, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11920 q = 1) (hb : d107483 q = 1) : d111275 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11924 q = 1) (hb : d107483 q = 1) : d11924 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11925 q = 1) (hb : d107483 q = 1) : d111276 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11925, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11926 q = 1) (hb : d107483 q = 1) : d111277 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11926, d111277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11926, d111277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11952 q = 1) (hb : d107483 q = 1) : d111298 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11952, d111298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11952, d111298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12026 q = 1) (hb : d107483 q = 1) : d111330 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12026, d111330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12026, d111330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro24867 (p : Pattern) (ha : d12032 p = 1) (hb : d107483 p = 1) : d111335 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11919 q = 1) (hb : d107483 q = 1) : d111274 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24853 q ha hb
    | true =>
      simp only [d11919, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11920 q = 1) (hb : d107483 q = 1) : d111275 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11924 q = 1) (hb : d107483 q = 1) : d11924 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11925 q = 1) (hb : d107483 q = 1) : d111276 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11925, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11960 q = 1) (hb : d107483 q = 1) : d111304 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11960, d111304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11960, d111304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11961 q = 1) (hb : d107483 q = 1) : d111305 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11961, d111305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11961, d111305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12032 q = 1) (hb : d107483 q = 1) : d111335 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12032, d111335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12032, d111335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro24868 (p : Pattern) (ha : d12037 p = 1) (hb : d107483 p = 1) : d111339 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11975 q = 1) (hb : d107483 q = 1) : d111312 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11975, d111312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24861 q ha hb
    | true =>
      simp only [d11975, d111312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11976 q = 1) (hb : d107483 q = 1) : d111313 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11976, d111313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11976, d111313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11919 q = 1) (hb : d107483 q = 1) : d111274 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24853 q ha hb
    | true =>
      simp only [d11919, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11920 q = 1) (hb : d107483 q = 1) : d111275 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11977 q = 1) (hb : d107483 q = 1) : d111314 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11977, d111314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11977, d111314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11978 q = 1) (hb : d107483 q = 1) : d111315 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11978, d111315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11978, d111315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11979 q = 1) (hb : d107483 q = 1) : d111316 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11979, d111316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11979, d111316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12037 q = 1) (hb : d107483 q = 1) : d111339 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12037, d111339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12037, d111339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24869 (p : Pattern) (ha : d12043 p = 1) (hb : d107483 p = 1) : d111342 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12014 q = 1) (hb : d107483 q = 1) : d111274 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12014, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24863 q ha hb
    | true =>
      simp only [d12014, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12015 q = 1) (hb : d107483 q = 1) : d111275 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12015, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12015, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12016 q = 1) (hb : d107483 q = 1) : d111320 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12016, d111320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12016, d111320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12017 q = 1) (hb : d107483 q = 1) : d111321 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12017, d111321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12017, d111321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12018 q = 1) (hb : d107483 q = 1) : d111322 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12018, d111322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12018, d111322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12043 q = 1) (hb : d107483 q = 1) : d111342 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12043, d111342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12043, d111342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24870 (p : Pattern) (ha : d107483 p = 1) (hb : d109032 p = 1) : d111348 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11955 q = 1) (hb : d107483 q = 1) : d11955 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11956 q = 1) (hb : d107483 q = 1) : d111300 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11956, d111300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24859 q ha hb
    | true =>
      simp only [d11956, d111300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11957 q = 1) (hb : d107483 q = 1) : d111301 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11957, d111301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11957, d111301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11958 q = 1) (hb : d107483 q = 1) : d111302 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11958, d111302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11958, d111302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11959 q = 1) (hb : d107483 q = 1) : d111303 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11959, d111303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11959, d111303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11965 q = 1) (hb : d107483 q = 1) : d11965 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11966 q = 1) (hb : d107483 q = 1) : d111307 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11966, d111307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24860 q ha hb
    | true =>
      simp only [d11966, d111307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11967 q = 1) (hb : d107483 q = 1) : d111308 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11967, d111308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11967, d111308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11968 q = 1) (hb : d107483 q = 1) : d111309 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11968, d111309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11968, d111309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11981 q = 1) (hb : d107483 q = 1) : d111318 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11981, d111318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24862 q ha hb
    | true =>
      simp only [d11981, d111318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24854 q ha hb
  have h11 (q : Pattern) (ha : d107483 q = 1) (hb : d109023 q = 1) : d111319 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109023, d111319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d109023, d111319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d12020 q = 1) (hb : d107483 q = 1) : d111324 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12020, d111324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24864 q ha hb
    | true =>
      simp only [d12020, d111324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12021 q = 1) (hb : d107483 q = 1) : d111325 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12021, d111325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12021, d111325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d107483 q = 1) (hb : d109024 q = 1) : d111326 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109024, d111326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109024, d111326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d107483 q = 1) (hb : d109025 q = 1) : d111327 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109025, d111327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d109025, d111327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107483 q = 1) (hb : d109026 q = 1) : d111328 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109026, d111328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d109026, d111328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12027 q = 1) (hb : d107483 q = 1) : d12027 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d12028 q = 1) (hb : d107483 q = 1) : d111331 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12028, d111331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24866 q ha hb
    | true =>
      simp only [d12028, d111331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12029 q = 1) (hb : d107483 q = 1) : d111332 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12029, d111332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12029, d111332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d12030 q = 1) (hb : d107483 q = 1) : d111333 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12030, d111333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d12030, d111333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d12031 q = 1) (hb : d107483 q = 1) : d111334 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12031, d111334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12031, d111334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d12033 q = 1) (hb : d107483 q = 1) : d12033 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d12034 q = 1) (hb : d107483 q = 1) : d111336 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12034, d111336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24867 q ha hb
    | true =>
      simp only [d12034, d111336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d12035 q = 1) (hb : d107483 q = 1) : d111337 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12035, d111337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12035, d111337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d12036 q = 1) (hb : d107483 q = 1) : d111338 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12036, d111338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12036, d111338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d12038 q = 1) (hb : d107483 q = 1) : d111340 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12038, d111340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24868 q ha hb
    | true =>
      simp only [d12038, d111340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24856 q ha hb
  have h27 (q : Pattern) (ha : d107483 q = 1) (hb : d109028 q = 1) : d111341 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109028, d111341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
    | true =>
      simp only [d109028, d111341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d12044 q = 1) (hb : d107483 q = 1) : d111343 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12044, d111343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24869 q ha hb
    | true =>
      simp only [d12044, d111343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d12045 q = 1) (hb : d107483 q = 1) : d111344 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12045, d111344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d12045, d111344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d107483 q = 1) (hb : d109029 q = 1) : d111345 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109029, d111345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d109029, d111345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d107483 q = 1) (hb : d109030 q = 1) : d111346 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109030, d111346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d109030, d111346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d107483 q = 1) (hb : d109031 q = 1) : d111347 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109031, d111347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d109031, d111347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d107483 q = 1) (hb : d109032 q = 1) : d111348 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109032, d111348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d109032, d111348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro24871 (p : Pattern) (ha : d107483 p = 1) (hb : d109039 p = 1) : d111357 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12038 q = 1) (hb : d107483 q = 1) : d111340 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12038, d111340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24868 q ha hb
    | true =>
      simp only [d12038, d111340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24856 q ha hb
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d109028 q = 1) : d111341 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109028, d111341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109028, d111341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d12044 q = 1) (hb : d107483 q = 1) : d111343 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12044, d111343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24869 q ha hb
    | true =>
      simp only [d12044, d111343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12045 q = 1) (hb : d107483 q = 1) : d111344 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12045, d111344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12045, d111344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d109029 q = 1) : d111345 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109029, d111345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109029, d111345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d109037 q = 1) : d111355 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109037, d111355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109037, d111355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107483 q = 1) (hb : d109038 q = 1) : d111356 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109038, d111356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109038, d111356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107483 q = 1) (hb : d109039 q = 1) : d111357 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109039, d111357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109039, d111357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24872 (p : Pattern) (ha : d12089 p = 1) (hb : d107483 p = 1) : d111364 p = 1 := by
  have h0 (q : Pattern) (ha : d12083 q = 1) (hb : d85721 q = 1) : d12083 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12087 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12088 q = 1) (hb : d107483 q = 1) : d111363 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12088, d107483, d111363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12088, d107483, d111363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12089 q = 1) (hb : d107483 q = 1) : d111364 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12089, d111364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12089, d111364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro24873 (p : Pattern) (ha : d12094 p = 1) (hb : d107483 p = 1) : d111368 p = 1 := by
  have h0 (q : Pattern) (ha : d12087 q = 1) (hb : d85721 q = 1) : d12087 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12092 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12093 q = 1) (hb : d107483 q = 1) : d111367 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12093, d107483, d111367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12093, d107483, d111367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12094 q = 1) (hb : d107483 q = 1) : d111368 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12094, d111368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12094, d111368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro24874 (p : Pattern) (ha : d12100 p = 1) (hb : d107483 p = 1) : d111374 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12090 q = 1) (hb : d107483 q = 1) : d111365 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12090, d111365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24872 q ha hb
    | true =>
      simp only [d12090, d111365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12091 q = 1) (hb : d107483 q = 1) : d111366 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12091, d111366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12091, d111366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12095 q = 1) (hb : d107483 q = 1) : d111369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12095, d111369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24873 q ha hb
    | true =>
      simp only [d12095, d111369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12096 q = 1) (hb : d107483 q = 1) : d111370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12096, d111370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12096, d111370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12097 q = 1) (hb : d107483 q = 1) : d111371 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12097, d111371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12097, d111371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12098 q = 1) (hb : d107483 q = 1) : d111372 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12098, d111372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12098, d111372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12099 q = 1) (hb : d107483 q = 1) : d111373 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12099, d111373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12099, d111373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12100 q = 1) (hb : d107483 q = 1) : d111374 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12100, d111374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12100, d111374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24875 (p : Pattern) (ha : d12108 p = 1) (hb : d107483 p = 1) : d111378 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12095 q = 1) (hb : d107483 q = 1) : d111369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12095, d111369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24873 q ha hb
    | true =>
      simp only [d12095, d111369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12096 q = 1) (hb : d107483 q = 1) : d111370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12096, d111370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12096, d111370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12104 q = 1) (hb : d107483 q = 1) : d12104 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12105 q = 1) (hb : d107483 q = 1) : d111375 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12105, d111375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12105, d111375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12106 q = 1) (hb : d107483 q = 1) : d111376 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12106, d111376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12106, d111376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12107 q = 1) (hb : d107483 q = 1) : d111377 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12107, d111377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12107, d111377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12108 q = 1) (hb : d107483 q = 1) : d111378 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12108, d111378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12108, d111378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro24876 (p : Pattern) (ha : d12141 p = 1) (hb : d107483 p = 1) : d111368 p = 1 := by
  have h0 (q : Pattern) (ha : d12087 q = 1) (hb : d85721 q = 1) : d12087 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12139 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12140 q = 1) (hb : d107483 q = 1) : d111367 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12140, d107483, d111367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12140, d107483, d111367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12141 q = 1) (hb : d107483 q = 1) : d111368 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12141, d111368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12141, d111368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro24877 (p : Pattern) (ha : d12147 p = 1) (hb : d107483 p = 1) : d111384 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12142 q = 1) (hb : d107483 q = 1) : d111369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12142, d111369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24876 q ha hb
    | true =>
      simp only [d12142, d111369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12143 q = 1) (hb : d107483 q = 1) : d111370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12143, d111370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12143, d111370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12144 q = 1) (hb : d107483 q = 1) : d111381 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12144, d111381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12144, d111381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12145 q = 1) (hb : d107483 q = 1) : d111382 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12145, d111382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12145, d111382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12146 q = 1) (hb : d107483 q = 1) : d111383 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12146, d111383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12146, d111383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12147 q = 1) (hb : d107483 q = 1) : d111384 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12147, d111384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12147, d111384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24878 (p : Pattern) (ha : d107483 p = 1) (hb : d109049 p = 1) : d111390 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12109 q = 1) (hb : d107483 q = 1) : d111379 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12109, d111379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24874 q ha hb
    | true =>
      simp only [d12109, d111379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24875 q ha hb
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d109045 q = 1) : d111380 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109045, d111380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109045, d111380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d12148 q = 1) (hb : d107483 q = 1) : d111385 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12148, d111385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24877 q ha hb
    | true =>
      simp only [d12148, d111385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12149 q = 1) (hb : d107483 q = 1) : d111386 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12149, d111386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12149, d111386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d109046 q = 1) : d111387 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109046, d111387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109046, d111387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d109047 q = 1) : d111388 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109047, d111388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109047, d111388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107483 q = 1) (hb : d109048 q = 1) : d111389 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109048, d111389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109048, d111389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107483 q = 1) (hb : d109049 q = 1) : d111390 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109049, d111390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109049, d111390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24879 (p : Pattern) (ha : d107483 p = 1) (hb : d109055 p = 1) : d111396 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11939 q = 1) (hb : d107483 q = 1) : d111286 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11939, d111286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11939, d111286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24855 q ha hb
  have h2 (q : Pattern) (ha : d11940 q = 1) (hb : d107483 q = 1) : d111287 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11940, d111287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11940, d111287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11949 q = 1) (hb : d107483 q = 1) : d111295 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11949, d111295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24855 q ha hb
    | true =>
      simp only [d11949, d111295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24857 q ha hb
  have h4 (q : Pattern) (ha : d11950 q = 1) (hb : d107483 q = 1) : d111296 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11950, d111296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11950, d111296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11951 q = 1) (hb : d107483 q = 1) : d111297 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11951, d111297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11951, d111297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d109033 q = 1) : d111349 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109033, d111349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24865 q ha hb
    | true =>
      simp only [d109033, d111349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24870 q ha hb
  have h7 (q : Pattern) (ha : d12062 q = 1) (hb : d107483 q = 1) : d12062 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12063 q = 1) (hb : d107483 q = 1) : d111351 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12063, d111351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24858 q ha hb
    | true =>
      simp only [d12063, d111351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107483 q = 1) (hb : d109034 q = 1) : d111352 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109034, d111352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109034, d111352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d107483 q = 1) (hb : d109035 q = 1) : d111353 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109035, d111353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109035, d111353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d107483 q = 1) (hb : d109036 q = 1) : d111354 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109036, d111354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d109036, d111354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d107483 q = 1) (hb : d109040 q = 1) : d111358 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109040, d111358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109040, d111358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24871 q ha hb
  have h13 (q : Pattern) (ha : d12072 q = 1) (hb : d107483 q = 1) : d12072 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d107483 q = 1) (hb : d109041 q = 1) : d111359 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109041, d111359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109041, d111359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d107483 q = 1) (hb : d109042 q = 1) : d111360 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109042, d111360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d109042, d111360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d107483 q = 1) (hb : d109043 q = 1) : d111361 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109043, d111361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d109043, d111361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d107483 q = 1) (hb : d109044 q = 1) : d111362 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109044, d111362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109044, d111362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d107483 q = 1) (hb : d109050 q = 1) : d111391 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109050, d111391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109050, d111391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24878 q ha hb
  have h19 (q : Pattern) (ha : d12165 q = 1) (hb : d107483 q = 1) : d12165 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d107483 q = 1) (hb : d109051 q = 1) : d111392 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109051, d111392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d109051, d111392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d107483 q = 1) (hb : d109052 q = 1) : d111393 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109052, d111393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d109052, d111393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d107483 q = 1) (hb : d109053 q = 1) : d111394 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109053, d111394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d109053, d111394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d107483 q = 1) (hb : d109054 q = 1) : d111395 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109054, d111395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d109054, d111395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d107483 q = 1) (hb : d109055 q = 1) : d111396 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109055, d111396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d109055, d111396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro24880 (p : Pattern) (ha : d107483 p = 1) (hb : d109061 p = 1) : d111402 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107483 q = 1) (hb : d109056 q = 1) : d111397 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109056, d111397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109056, d111397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24879 q ha hb
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d109057 q = 1) : d111398 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109057, d111398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109057, d111398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d109058 q = 1) : d111399 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109058, d111399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109058, d111399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d109059 q = 1) : d111400 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109059, d111400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109059, d111400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d109060 q = 1) : d111401 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109060, d111401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109060, d111401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d109061 q = 1) : d111402 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109061, d111402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109061, d111402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24881 (p : Pattern) (ha : d107483 p = 1) (hb : d109067 p = 1) : d111408 p = 1 := by
  have h0 (q : Pattern) (ha : d107483 q = 1) (hb : d108896 q = 1) : d110869 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108896, d110869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24742 q ha hb
    | true =>
      simp only [d108896, d110869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24768 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d108936 q = 1) : d111001 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108936, d111001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108936, d111001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24796 q ha hb
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d108937 q = 1) : d111002 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108937, d111002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108937, d111002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d108977 q = 1) : d111134 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108977, d111134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108977, d111134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24824 q ha hb
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d108978 q = 1) : d111135 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108978, d111135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108978, d111135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d108979 q = 1) : d111136 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d108979, d111136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108979, d111136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107483 q = 1) (hb : d109019 q = 1) : d111268 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109019, d111268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109019, d111268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24852 q ha hb
  have h8 (q : Pattern) (ha : d107483 q = 1) (hb : d109020 q = 1) : d111269 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109020, d111269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109020, d111269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107483 q = 1) (hb : d109021 q = 1) : d111270 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d109021, d111270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109021, d111270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107483 q = 1) (hb : d109022 q = 1) : d111271 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d109022, d111271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109022, d111271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107483 q = 1) (hb : d109062 q = 1) : d111403 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109062, d111403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109062, d111403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24880 q ha hb
  have h12 (q : Pattern) (ha : d107483 q = 1) (hb : d109063 q = 1) : d111404 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109063, d111404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109063, d111404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d107483 q = 1) (hb : d109064 q = 1) : d111405 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d109064, d111405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109064, d111405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d107483 q = 1) (hb : d109065 q = 1) : d111406 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d109065, d111406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109065, d111406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d107483 q = 1) (hb : d109066 q = 1) : d111407 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d109066, d111407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109066, d111407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107483 q = 1) (hb : d109067 q = 1) : d111408 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d109067, d111408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d109067, d111408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro24882 (p : Pattern) (ha : d107483 p = 1) (hb : d109073 p = 1) : d111414 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107483 q = 1) (hb : d109068 q = 1) : d111409 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d109068, d111409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24881 q ha hb
    | true =>
      simp only [d109068, d111409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d109069 q = 1) : d111410 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d109069, d111410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109069, d111410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d109070 q = 1) : d111411 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d109070, d111411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109070, d111411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d109071 q = 1) : d111412 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d109071, d111412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109071, d111412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d109072 q = 1) : d111413 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d109072, d111413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109072, d111413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d109073 q = 1) : d111414 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d109073, d111414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109073, d111414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24883 (p : Pattern) (ha : d107483 p = 1) (hb : d109079 p = 1) : d111420 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107483 q = 1) (hb : d109074 q = 1) : d111415 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d109074, d111415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24882 q ha hb
    | true =>
      simp only [d109074, d111415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d109075 q = 1) : d111416 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d109075, d111416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109075, d111416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d109076 q = 1) : d111417 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d109076, d111417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109076, d111417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d109077 q = 1) : d111418 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d109077, d111418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109077, d111418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d109078 q = 1) : d111419 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d109078, d111419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109078, d111419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d109079 q = 1) : d111420 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d109079, d111420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109079, d111420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24884 (p : Pattern) (ha : d107483 p = 1) (hb : d109085 p = 1) : d111426 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107483 q = 1) (hb : d109080 q = 1) : d111421 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d109080, d111421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24883 q ha hb
    | true =>
      simp only [d109080, d111421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d109081 q = 1) : d111422 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d109081, d111422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109081, d111422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d109082 q = 1) : d111423 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d109082, d111423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109082, d111423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d109083 q = 1) : d111424 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d109083, d111424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109083, d111424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d109084 q = 1) : d111425 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d109084, d111425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109084, d111425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d109085 q = 1) : d111426 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d109085, d111426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109085, d111426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24885 (p : Pattern) (ha : d107483 p = 1) (hb : d109091 p = 1) : d111432 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107483 q = 1) (hb : d109086 q = 1) : d111427 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d109086, d111427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24884 q ha hb
    | true =>
      simp only [d109086, d111427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d109087 q = 1) : d111428 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d109087, d111428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109087, d111428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d109088 q = 1) : d111429 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d109088, d111429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109088, d111429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d109089 q = 1) : d111430 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d109089, d111430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109089, d111430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d109090 q = 1) : d111431 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d109090, d111431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109090, d111431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d109091 q = 1) : d111432 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d109091, d111432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109091, d111432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24886 (p : Pattern) (ha : d107483 p = 1) (hb : d109097 p = 1) : d111438 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107483 q = 1) (hb : d109092 q = 1) : d111433 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d109092, d111433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24885 q ha hb
    | true =>
      simp only [d109092, d111433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d109093 q = 1) : d111434 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d109093, d111434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109093, d111434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d109094 q = 1) : d111435 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d109094, d111435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109094, d111435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d109095 q = 1) : d111436 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d109095, d111436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109095, d111436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d109096 q = 1) : d111437 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d109096, d111437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109096, d111437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d109097 q = 1) : d111438 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d109097, d111438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109097, d111438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24887 (p : Pattern) (ha : d107483 p = 1) (hb : d109103 p = 1) : d111444 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107483 q = 1) (hb : d109098 q = 1) : d111439 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d109098, d111439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24886 q ha hb
    | true =>
      simp only [d109098, d111439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d109099 q = 1) : d111440 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d109099, d111440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109099, d111440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d109100 q = 1) : d111441 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d109100, d111441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109100, d111441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d109101 q = 1) : d111442 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d109101, d111442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109101, d111442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d109102 q = 1) : d111443 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d109102, d111443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109102, d111443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d109103 q = 1) : d111444 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d109103, d111444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109103, d111444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24888 (p : Pattern) (ha : d107483 p = 1) (hb : d109109 p = 1) : d111450 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107483 q = 1) (hb : d109104 q = 1) : d111445 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d109104, d111445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24887 q ha hb
    | true =>
      simp only [d109104, d111445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d109105 q = 1) : d111446 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d109105, d111446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109105, d111446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d109106 q = 1) : d111447 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d109106, d111447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109106, d111447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d109107 q = 1) : d111448 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d109107, d111448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109107, d111448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d109108 q = 1) : d111449 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d109108, d111449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109108, d111449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d109109 q = 1) : d111450 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d109109, d111450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109109, d111450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24889 (p : Pattern) (ha : d83664 p = 1) (hb : d110577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51882 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10649 q = 1) (hb : d51996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
    | true =>
      simp only [d10649, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10650 q = 1) (hb : d51997 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10650, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10651 q = 1) (hb : d51998 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10651, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31 q = 1) (hb : d51883 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
    | true =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32 q = 1) (hb : d51884 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33 q = 1) (hb : d51885 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10652 q = 1) (hb : d51999 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10652, d51999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10652, d51999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83663 q = 1) (hb : d110576 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d83663, d110576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d83663, d110576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d83664 q = 1) (hb : d110577 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d83664, d110577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d83664, d110577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro24890 (p : Pattern) (ha : d83670 p = 1) (hb : d110583 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83665 q = 1) (hb : d110578 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83665, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24889 q ha hb
    | true =>
      simp only [d83665, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83666 q = 1) (hb : d110579 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83666, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83666, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d83667 q = 1) (hb : d110580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83667, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83667, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83668 q = 1) (hb : d110581 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83668, d110581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83668, d110581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83669 q = 1) (hb : d110582 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83669, d110582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83669, d110582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83670 q = 1) (hb : d110583 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83670, d110583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83670, d110583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24891 (p : Pattern) (ha : d83676 p = 1) (hb : d110589 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d83671 q = 1) (hb : d110584 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83671, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24890 q ha hb
    | true =>
      simp only [d83671, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d83672 q = 1) (hb : d110585 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83672, d110585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83672, d110585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h13 (q : Pattern) (ha : d83673 q = 1) (hb : d110586 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83673, d110586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83673, d110586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d83674 q = 1) (hb : d110587 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83674, d110587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d83674, d110587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83675 q = 1) (hb : d110588 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83675, d110588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d83675, d110588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d83676 q = 1) (hb : d110589 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83676, d110589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83676, d110589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro24892 (p : Pattern) (ha : d83677 p = 1) (hb : d110590 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83665 q = 1) (hb : d110578 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83665, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24889 q ha hb
    | true =>
      simp only [d83665, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83666 q = 1) (hb : d110579 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83666, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83666, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d83667 q = 1) (hb : d110580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83667, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83667, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83668 q = 1) (hb : d110581 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83668, d110581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83668, d110581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83669 q = 1) (hb : d110582 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83669, d110582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83669, d110582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83677 q = 1) (hb : d110590 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83677, d110590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83677, d110590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24893 (p : Pattern) (ha : d83683 p = 1) (hb : d110596 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d83671 q = 1) (hb : d110584 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83671, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24890 q ha hb
    | true =>
      simp only [d83671, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d83672 q = 1) (hb : d110585 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83672, d110585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83672, d110585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h13 (q : Pattern) (ha : d83673 q = 1) (hb : d110586 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83673, d110586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83673, d110586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d83674 q = 1) (hb : d110587 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83674, d110587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d83674, d110587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83675 q = 1) (hb : d110588 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83675, d110588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d83675, d110588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h23 (q : Pattern) (ha : d83678 q = 1) (hb : d110591 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83678, d110591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24892 q ha hb
    | true =>
      simp only [d83678, d110591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d83679 q = 1) (hb : d110592 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83679, d110592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d83679, d110592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h28 (q : Pattern) (ha : d83680 q = 1) (hb : d110593 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83680, d110593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d83680, d110593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d83681 q = 1) (hb : d110594 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83681, d110594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d83681, d110594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d83682 q = 1) (hb : d110595 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83682, d110595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d83682, d110595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d83683 q = 1) (hb : d110596 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83683, d110596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d83683, d110596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro24894 (p : Pattern) (ha : d83690 p = 1) (hb : d110603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83678 q = 1) (hb : d110591 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83678, d110591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24892 q ha hb
    | true =>
      simp only [d83678, d110591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83679 q = 1) (hb : d110592 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83679, d110592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83679, d110592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h6 (q : Pattern) (ha : d83680 q = 1) (hb : d110593 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83680, d110593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83680, d110593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d83688 q = 1) (hb : d110601 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83688, d110601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83688, d110601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83689 q = 1) (hb : d110602 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83689, d110602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83689, d110602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83690 q = 1) (hb : d110603 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83690, d110603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83690, d110603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro24895 (p : Pattern) (ha : d83697 p = 1) (hb : d110610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51923 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10686 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
    | true =>
      simp only [d10686, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10687 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10687, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10688 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10688, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d72 q = 1) (hb : d51924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
    | true =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d73 q = 1) (hb : d51925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10689 q = 1) (hb : d52053 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10689, d52053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10689, d52053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83696 q = 1) (hb : d110609 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d83696, d110609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d83696, d110609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d83697 q = 1) (hb : d110610 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d83697, d110610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d83697, d110610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro24896 (p : Pattern) (ha : d83703 p = 1) (hb : d110616 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83698 q = 1) (hb : d110611 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83698, d110611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24895 q ha hb
    | true =>
      simp only [d83698, d110611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83699 q = 1) (hb : d110612 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83699, d110612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83699, d110612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d83700 q = 1) (hb : d110613 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83700, d110613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83700, d110613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83701 q = 1) (hb : d110614 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83701, d110614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83701, d110614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83702 q = 1) (hb : d110615 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83702, d110615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83702, d110615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83703 q = 1) (hb : d110616 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83703, d110616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83703, d110616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24897 (p : Pattern) (ha : d83709 p = 1) (hb : d110622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83704 q = 1) (hb : d110617 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83704, d110617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24896 q ha hb
    | true =>
      simp only [d83704, d110617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83705 q = 1) (hb : d110618 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83705, d110618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83705, d110618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h6 (q : Pattern) (ha : d83706 q = 1) (hb : d110619 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83706, d110619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83706, d110619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d83707 q = 1) (hb : d110620 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83707, d110620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83707, d110620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83708 q = 1) (hb : d110621 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83708, d110621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83708, d110621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83709 q = 1) (hb : d110622 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83709, d110622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83709, d110622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro24898 (p : Pattern) (ha : d83715 p = 1) (hb : d110628 p = 1) : d0 p = 1 := by
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
  have h6 (q : Pattern) (ha : d83684 q = 1) (hb : d110597 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83684, d110597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24891 q ha hb
    | true =>
      simp only [d83684, d110597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24893 q ha hb
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
  have h8 (q : Pattern) (ha : d83685 q = 1) (hb : d110598 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83685, d110598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83685, d110598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d83686 q = 1) (hb : d110599 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83686, d110599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83686, d110599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d83687 q = 1) (hb : d110600 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83687, d110600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d83687, d110600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d83691 q = 1) (hb : d110604 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83691, d110604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83691, d110604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24894 q ha hb
  have h12 (q : Pattern) (ha : d83692 q = 1) (hb : d110605 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83692, d110605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d83692, d110605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d83693 q = 1) (hb : d110606 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83693, d110606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d83693, d110606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d83694 q = 1) (hb : d110607 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83694, d110607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d83694, d110607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d83695 q = 1) (hb : d110608 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83695, d110608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83695, d110608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d83710 q = 1) (hb : d110623 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83710, d110623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83710, d110623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24897 q ha hb
  have h17 (q : Pattern) (ha : d83711 q = 1) (hb : d110624 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83711, d110624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d83711, d110624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d83712 q = 1) (hb : d110625 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83712, d110625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d83712, d110625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d83713 q = 1) (hb : d110626 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83713, d110626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d83713, d110626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d83714 q = 1) (hb : d110627 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83714, d110627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d83714, d110627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d83715 q = 1) (hb : d110628 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d83715, d110628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d83715, d110628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro24899 (p : Pattern) (ha : d83725 p = 1) (hb : d110638 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83671 q = 1) (hb : d110584 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83671, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24890 q ha hb
    | true =>
      simp only [d83671, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d83721 q = 1) (hb : d110634 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83721, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83721, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83722 q = 1) (hb : d110635 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83722, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83722, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83723 q = 1) (hb : d110636 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83723, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83723, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83724 q = 1) (hb : d110637 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83724, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83724, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83725 q = 1) (hb : d110638 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83725, d110638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83725, d110638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24900 (p : Pattern) (ha : d83732 p = 1) (hb : d110645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83671 q = 1) (hb : d110584 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83671, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24890 q ha hb
    | true =>
      simp only [d83671, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d83721 q = 1) (hb : d110634 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83721, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83721, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83722 q = 1) (hb : d110635 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83722, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83722, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83723 q = 1) (hb : d110636 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83723, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83723, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83724 q = 1) (hb : d110637 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83724, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83724, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83678 q = 1) (hb : d110591 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83678, d110591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24892 q ha hb
    | true =>
      simp only [d83678, d110591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h7 (q : Pattern) (ha : d83728 q = 1) (hb : d110641 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83728, d110641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83728, d110641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83729 q = 1) (hb : d110642 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83729, d110642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83729, d110642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d83730 q = 1) (hb : d110643 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83730, d110643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83730, d110643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83731 q = 1) (hb : d110644 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83731, d110644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83731, d110644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d83732 q = 1) (hb : d110645 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83732, d110645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83732, d110645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24901 (p : Pattern) (ha : d83737 p = 1) (hb : d110650 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83665 q = 1) (hb : d110578 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83665, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24889 q ha hb
    | true =>
      simp only [d83665, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83666 q = 1) (hb : d110579 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83666, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83666, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d83667 q = 1) (hb : d110580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83667, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83667, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83668 q = 1) (hb : d110581 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83668, d110581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83668, d110581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83736 q = 1) (hb : d110649 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83736, d110649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83736, d110649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83737 q = 1) (hb : d110650 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83737, d110650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83737, d110650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24902 (p : Pattern) (ha : d83744 p = 1) (hb : d110657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83665 q = 1) (hb : d110578 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83665, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24889 q ha hb
    | true =>
      simp only [d83665, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83666 q = 1) (hb : d110579 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83666, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83666, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d83667 q = 1) (hb : d110580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83667, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83667, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83742 q = 1) (hb : d110655 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83742, d110655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83742, d110655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83743 q = 1) (hb : d110656 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83743, d110656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83743, d110656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83744 q = 1) (hb : d110657 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83744, d110657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83744, d110657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24903 (p : Pattern) (ha : d83749 p = 1) (hb : d110662 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51995 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10742 q = 1) (hb : d52124 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10742, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43 q ha hb
    | true =>
      simp only [d10742, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10743 q = 1) (hb : d52125 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10743, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10743, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10744 q = 1) (hb : d52126 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10744, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10744, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d51882 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10649 q = 1) (hb : d51996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
    | true =>
      simp only [d10649, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10650 q = 1) (hb : d51997 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10650, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10651 q = 1) (hb : d51998 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10651, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10745 q = 1) (hb : d52127 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10745, d52127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10745, d52127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83748 q = 1) (hb : d110661 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d83748, d110661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d83748, d110661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d83749 q = 1) (hb : d110662 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d83749, d110662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83749, d110662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro24904 (p : Pattern) (ha : d83755 p = 1) (hb : d110668 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83750 q = 1) (hb : d110663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83750, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24903 q ha hb
    | true =>
      simp only [d83750, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83751 q = 1) (hb : d110664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83751, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83751, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83665 q = 1) (hb : d110578 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83665, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24889 q ha hb
    | true =>
      simp only [d83665, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83666 q = 1) (hb : d110579 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83666, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83666, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83752 q = 1) (hb : d110665 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83752, d110665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83752, d110665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83753 q = 1) (hb : d110666 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83753, d110666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83753, d110666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83754 q = 1) (hb : d110667 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83754, d110667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83754, d110667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83755 q = 1) (hb : d110668 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83755, d110668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83755, d110668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24905 (p : Pattern) (ha : d83761 p = 1) (hb : d110674 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83665 q = 1) (hb : d110578 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83665, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24889 q ha hb
    | true =>
      simp only [d83665, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83666 q = 1) (hb : d110579 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83666, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83666, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83758 q = 1) (hb : d110671 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83758, d110671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83758, d110671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83759 q = 1) (hb : d110672 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83759, d110672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83759, d110672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83760 q = 1) (hb : d110673 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83760, d110673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83760, d110673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83761 q = 1) (hb : d110674 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83761, d110674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83761, d110674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24906 (p : Pattern) (ha : d83767 p = 1) (hb : d110680 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83738 q = 1) (hb : d110651 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83738, d110651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24901 q ha hb
    | true =>
      simp only [d83738, d110651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d83739 q = 1) (hb : d110652 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83739, d110652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83739, d110652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83740 q = 1) (hb : d110653 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83740, d110653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83740, d110653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83741 q = 1) (hb : d110654 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83741, d110654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83741, d110654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83745 q = 1) (hb : d110658 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83745, d110658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24902 q ha hb
    | true =>
      simp only [d83745, d110658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d83746 q = 1) (hb : d110659 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83746, d110659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83746, d110659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83747 q = 1) (hb : d110660 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83747, d110660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83747, d110660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83756 q = 1) (hb : d110669 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83756, d110669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24904 q ha hb
    | true =>
      simp only [d83756, d110669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24890 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d83671 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d83757 q = 1) (hb : d110670 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83757, d110670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83757, d110670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d83762 q = 1) (hb : d110675 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83762, d110675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24905 q ha hb
    | true =>
      simp only [d83762, d110675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d83763 q = 1) (hb : d110676 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83763, d110676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d83763, d110676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d83764 q = 1) (hb : d110677 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83764, d110677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83764, d110677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d83765 q = 1) (hb : d110678 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83765, d110678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83765, d110678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83766 q = 1) (hb : d110679 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83766, d110679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83766, d110679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d83767 q = 1) (hb : d110680 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83767, d110680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83767, d110680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro24907 (p : Pattern) (ha : d83768 p = 1) (hb : d110681 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83665 q = 1) (hb : d110578 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83665, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24889 q ha hb
    | true =>
      simp only [d83665, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83666 q = 1) (hb : d110579 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83666, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83666, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d83667 q = 1) (hb : d110580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83667, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83667, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83668 q = 1) (hb : d110581 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83668, d110581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83668, d110581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83736 q = 1) (hb : d110649 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83736, d110649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83736, d110649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83768 q = 1) (hb : d110681 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83768, d110681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83768, d110681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24908 (p : Pattern) (ha : d83773 p = 1) (hb : d110686 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83665 q = 1) (hb : d110578 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83665, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24889 q ha hb
    | true =>
      simp only [d83665, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83666 q = 1) (hb : d110579 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83666, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83666, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d83667 q = 1) (hb : d110580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83667, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83667, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83742 q = 1) (hb : d110655 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83742, d110655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83742, d110655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83743 q = 1) (hb : d110656 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83743, d110656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83743, d110656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83773 q = 1) (hb : d110686 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83773, d110686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83773, d110686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24909 (p : Pattern) (ha : d83777 p = 1) (hb : d110690 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83750 q = 1) (hb : d110663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83750, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24903 q ha hb
    | true =>
      simp only [d83750, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83751 q = 1) (hb : d110664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83751, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83751, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83665 q = 1) (hb : d110578 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83665, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24889 q ha hb
    | true =>
      simp only [d83665, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83666 q = 1) (hb : d110579 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83666, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83666, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83752 q = 1) (hb : d110665 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83752, d110665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83752, d110665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83753 q = 1) (hb : d110666 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83753, d110666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83753, d110666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83754 q = 1) (hb : d110667 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83754, d110667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83754, d110667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83777 q = 1) (hb : d110690 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83777, d110690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83777, d110690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24910 (p : Pattern) (ha : d83780 p = 1) (hb : d110693 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83665 q = 1) (hb : d110578 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83665, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24889 q ha hb
    | true =>
      simp only [d83665, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83666 q = 1) (hb : d110579 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83666, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83666, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83758 q = 1) (hb : d110671 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83758, d110671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83758, d110671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83759 q = 1) (hb : d110672 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83759, d110672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83759, d110672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83760 q = 1) (hb : d110673 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83760, d110673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83760, d110673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83780 q = 1) (hb : d110693 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83780, d110693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83780, d110693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24911 (p : Pattern) (ha : d83786 p = 1) (hb : d110699 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83738 q = 1) (hb : d110651 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83738, d110651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24901 q ha hb
    | true =>
      simp only [d83738, d110651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d83739 q = 1) (hb : d110652 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83739, d110652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83739, d110652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83740 q = 1) (hb : d110653 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83740, d110653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83740, d110653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83741 q = 1) (hb : d110654 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83741, d110654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83741, d110654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83745 q = 1) (hb : d110658 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83745, d110658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24902 q ha hb
    | true =>
      simp only [d83745, d110658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d83746 q = 1) (hb : d110659 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83746, d110659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83746, d110659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83747 q = 1) (hb : d110660 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83747, d110660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83747, d110660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83756 q = 1) (hb : d110669 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83756, d110669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24904 q ha hb
    | true =>
      simp only [d83756, d110669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24890 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d83671 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d83757 q = 1) (hb : d110670 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83757, d110670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83757, d110670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d83762 q = 1) (hb : d110675 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83762, d110675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24905 q ha hb
    | true =>
      simp only [d83762, d110675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d83763 q = 1) (hb : d110676 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83763, d110676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d83763, d110676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d83764 q = 1) (hb : d110677 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83764, d110677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83764, d110677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d83765 q = 1) (hb : d110678 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83765, d110678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83765, d110678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83766 q = 1) (hb : d110679 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83766, d110679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83766, d110679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d83769 q = 1) (hb : d110682 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83769, d110682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24907 q ha hb
    | true =>
      simp only [d83769, d110682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q hb ha
  have h17 (q : Pattern) (ha : d83770 q = 1) (hb : d110683 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83770, d110683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83770, d110683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d83771 q = 1) (hb : d110684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83771, d110684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d83771, d110684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d83772 q = 1) (hb : d110685 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83772, d110685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83772, d110685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d83774 q = 1) (hb : d110687 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83774, d110687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24908 q ha hb
    | true =>
      simp only [d83774, d110687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q hb ha
  have h21 (q : Pattern) (ha : d83775 q = 1) (hb : d110688 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83775, d110688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83775, d110688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d83776 q = 1) (hb : d110689 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83776, d110689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d83776, d110689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d83778 q = 1) (hb : d110691 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83778, d110691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24909 q ha hb
    | true =>
      simp only [d83778, d110691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24892 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d83678 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d83779 q = 1) (hb : d110692 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83779, d110692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d83779, d110692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d83781 q = 1) (hb : d110694 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83781, d110694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24910 q ha hb
    | true =>
      simp only [d83781, d110694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d83782 q = 1) (hb : d110695 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83782, d110695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d83782, d110695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d83783 q = 1) (hb : d110696 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83783, d110696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d83783, d110696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d83784 q = 1) (hb : d110697 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83784, d110697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d83784, d110697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d83785 q = 1) (hb : d110698 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83785, d110698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d83785, d110698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d83786 q = 1) (hb : d110699 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83786, d110699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d83786, d110699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro24912 (p : Pattern) (ha : d83788 p = 1) (hb : d110701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83671 q = 1) (hb : d110584 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83671, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24890 q ha hb
    | true =>
      simp only [d83671, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d83721 q = 1) (hb : d110634 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83721, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83721, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83722 q = 1) (hb : d110635 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83722, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83722, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83723 q = 1) (hb : d110636 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83723, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83723, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83724 q = 1) (hb : d110637 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83724, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83724, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h11 (q : Pattern) (ha : d83788 q = 1) (hb : d110701 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83788, d110701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83788, d110701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro24913 (p : Pattern) (ha : d83795 p = 1) (hb : d110708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83778 q = 1) (hb : d110691 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83778, d110691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24909 q ha hb
    | true =>
      simp only [d83778, d110691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24892 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83678 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83779 q = 1) (hb : d110692 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83779, d110692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83779, d110692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d83781 q = 1) (hb : d110694 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83781, d110694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24910 q ha hb
    | true =>
      simp only [d83781, d110694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83782 q = 1) (hb : d110695 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83782, d110695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83782, d110695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83783 q = 1) (hb : d110696 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83783, d110696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83783, d110696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83793 q = 1) (hb : d110706 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83793, d110706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83793, d110706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83794 q = 1) (hb : d110707 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83794, d110707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83794, d110707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83795 q = 1) (hb : d110708 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83795, d110708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83795, d110708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro24914 (p : Pattern) (ha : d83802 p = 1) (hb : d110715 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52049 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10814 q = 1) (hb : d52184 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10814, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47 q ha hb
    | true =>
      simp only [d10814, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10815 q = 1) (hb : d52185 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10815, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10815, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10816 q = 1) (hb : d52186 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10816, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10816, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d51923 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10686 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
    | true =>
      simp only [d10686, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10687 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10687, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10688 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10688, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10817 q = 1) (hb : d52187 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10817, d52187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10817, d52187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83801 q = 1) (hb : d110714 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d83801, d110714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d83801, d110714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d83802 q = 1) (hb : d110715 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d83802, d110715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83802, d110715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro24915 (p : Pattern) (ha : d83808 p = 1) (hb : d110721 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83803 q = 1) (hb : d110716 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83803, d110716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24914 q ha hb
    | true =>
      simp only [d83803, d110716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83804 q = 1) (hb : d110717 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83804, d110717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83804, d110717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83698 q = 1) (hb : d110611 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83698, d110611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24895 q ha hb
    | true =>
      simp only [d83698, d110611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83699 q = 1) (hb : d110612 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83699, d110612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83699, d110612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83805 q = 1) (hb : d110718 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83805, d110718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83805, d110718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83806 q = 1) (hb : d110719 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83806, d110719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83806, d110719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83807 q = 1) (hb : d110720 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83807, d110720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83807, d110720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83808 q = 1) (hb : d110721 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83808, d110721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83808, d110721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24916 (p : Pattern) (ha : d83814 p = 1) (hb : d110727 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83698 q = 1) (hb : d110611 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83698, d110611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24895 q ha hb
    | true =>
      simp only [d83698, d110611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83699 q = 1) (hb : d110612 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83699, d110612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83699, d110612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83811 q = 1) (hb : d110724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83811, d110724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83811, d110724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83812 q = 1) (hb : d110725 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83812, d110725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83812, d110725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83813 q = 1) (hb : d110726 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83813, d110726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83813, d110726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83814 q = 1) (hb : d110727 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83814, d110727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83814, d110727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24917 (p : Pattern) (ha : d83820 p = 1) (hb : d110733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83809 q = 1) (hb : d110722 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83809, d110722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24915 q ha hb
    | true =>
      simp only [d83809, d110722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24896 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83704 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83810 q = 1) (hb : d110723 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83810, d110723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83810, d110723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d83815 q = 1) (hb : d110728 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83815, d110728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24916 q ha hb
    | true =>
      simp only [d83815, d110728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83816 q = 1) (hb : d110729 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83816, d110729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83816, d110729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83817 q = 1) (hb : d110730 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83817, d110730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83817, d110730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83818 q = 1) (hb : d110731 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83818, d110731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83818, d110731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83819 q = 1) (hb : d110732 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83819, d110732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83819, d110732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83820 q = 1) (hb : d110733 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83820, d110733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83820, d110733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro24918 (p : Pattern) (ha : d83826 p = 1) (hb : d110739 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83726 q = 1) (hb : d110639 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83726, d110639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83726, d110639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24899 q ha hb
  have h2 (q : Pattern) (ha : d83727 q = 1) (hb : d110640 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83727, d110640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83727, d110640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d83733 q = 1) (hb : d110646 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83733, d110646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24899 q ha hb
    | true =>
      simp only [d83733, d110646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24900 q ha hb
  have h4 (q : Pattern) (ha : d83734 q = 1) (hb : d110647 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83734, d110647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83734, d110647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83735 q = 1) (hb : d110648 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83735, d110648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83735, d110648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83787 q = 1) (hb : d110700 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83787, d110700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24906 q ha hb
    | true =>
      simp only [d83787, d110700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24911 q ha hb
  have h7 (q : Pattern) (ha : d83789 q = 1) (hb : d110702 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83789, d110702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24912 q ha hb
    | true =>
      simp only [d83789, d110702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q hb ha
  have h8 (q : Pattern) (ha : d83790 q = 1) (hb : d110703 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83790, d110703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83790, d110703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83791 q = 1) (hb : d110704 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83791, d110704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83791, d110704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d83792 q = 1) (hb : d110705 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83792, d110705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83792, d110705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d83796 q = 1) (hb : d110709 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83796, d110709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83796, d110709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24913 q ha hb
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
  have h13 (q : Pattern) (ha : d83797 q = 1) (hb : d110710 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83797, d110710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d83797, d110710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d83798 q = 1) (hb : d110711 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83798, d110711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d83798, d110711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d83799 q = 1) (hb : d110712 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83799, d110712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d83799, d110712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d83800 q = 1) (hb : d110713 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83800, d110713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83800, d110713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d83821 q = 1) (hb : d110734 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83821, d110734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83821, d110734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24917 q ha hb
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
  have h19 (q : Pattern) (ha : d83822 q = 1) (hb : d110735 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83822, d110735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d83822, d110735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d83823 q = 1) (hb : d110736 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83823, d110736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d83823, d110736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d83824 q = 1) (hb : d110737 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83824, d110737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d83824, d110737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d83825 q = 1) (hb : d110738 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83825, d110738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d83825, d110738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d83826 q = 1) (hb : d110739 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d83826, d110739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d83826, d110739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro24919 (p : Pattern) (ha : d83832 p = 1) (hb : d110745 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d83716 q = 1) (hb : d110629 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d83716, d110629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83716, d110629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24898 q ha hb
  have h6 (q : Pattern) (ha : d83717 q = 1) (hb : d110630 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d83717, d110630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83717, d110630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83718 q = 1) (hb : d110631 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d83718, d110631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83718, d110631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83719 q = 1) (hb : d110632 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d83719, d110632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83719, d110632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83720 q = 1) (hb : d110633 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d83720, d110633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d83720, d110633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83827 q = 1) (hb : d110740 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d83827, d110740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83827, d110740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24918 q ha hb
  have h11 (q : Pattern) (ha : d83828 q = 1) (hb : d110741 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d83828, d110741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83828, d110741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d83829 q = 1) (hb : d110742 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d83829, d110742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83829, d110742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d83830 q = 1) (hb : d110743 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d83830, d110743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83830, d110743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d83831 q = 1) (hb : d110744 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d83831, d110744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83831, d110744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83832 q = 1) (hb : d110745 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d83832, d110745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d83832, d110745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro24920 (p : Pattern) (ha : d10869 p = 1) (hb : d52228 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51882 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10649 q = 1) (hb : d51996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
    | true =>
      simp only [d10649, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10650 q = 1) (hb : d51997 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10650, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10651 q = 1) (hb : d51998 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10651, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10863 q = 1) (hb : d52222 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10863, d52222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10863, d52222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10868 q = 1) (hb : d52227 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10868, d52227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10868, d52227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10869 q = 1) (hb : d52228 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10869, d52228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10869, d52228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro24921 (p : Pattern) (ha : d10879 p = 1) (hb : d52238 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10870 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24920 q ha hb
    | true =>
      simp only [d10870, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10871 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10876 q = 1) (hb : d52235 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d52235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10876, d52235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10877 q = 1) (hb : d52236 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10877, d52236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10877, d52236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10878 q = 1) (hb : d52237 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10878, d52237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10878, d52237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10879 q = 1) (hb : d52238 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10879, d52238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10879, d52238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24922 (p : Pattern) (ha : d10889 p = 1) (hb : d52248 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10870 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24920 q ha hb
    | true =>
      simp only [d10870, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10871 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10876 q = 1) (hb : d52235 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d52235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10876, d52235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10877 q = 1) (hb : d52236 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10877, d52236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10877, d52236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10878 q = 1) (hb : d52237 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10878, d52237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10878, d52237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10889 q = 1) (hb : d52248 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10889, d52248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10889, d52248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24923 (p : Pattern) (ha : d10998 p = 1) (hb : d52348 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10987 q = 1) (hb : d52337 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10987, d52337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24921 q ha hb
    | true =>
      simp only [d10987, d52337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10988 q = 1) (hb : d52338 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10988, d52338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10988, d52338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10989 q = 1) (hb : d52339 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10989, d52339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10989, d52339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10990 q = 1) (hb : d52340 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10990, d52340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10990, d52340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10991 q = 1) (hb : d52341 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10991, d52341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10991, d52341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10993 q = 1) (hb : d52343 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10993, d52343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24922 q ha hb
    | true =>
      simp only [d10993, d52343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10994 q = 1) (hb : d52344 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10994, d52344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10994, d52344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10995 q = 1) (hb : d52345 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10995, d52345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10995, d52345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d10996 q = 1) (hb : d52346 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10996, d52346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10996, d52346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10997 q = 1) (hb : d52347 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10997, d52347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10997, d52347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10998 q = 1) (hb : d52348 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10998, d52348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10998, d52348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24924 (p : Pattern) (ha : d11007 p = 1) (hb : d52357 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10993 q = 1) (hb : d52343 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10993, d52343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24922 q ha hb
    | true =>
      simp only [d10993, d52343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10994 q = 1) (hb : d52344 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10994, d52344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10994, d52344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10995 q = 1) (hb : d52345 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10995, d52345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10995, d52345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10996 q = 1) (hb : d52346 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10996, d52346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10996, d52346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10997 q = 1) (hb : d52347 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10997, d52347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10997, d52347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11007 q = 1) (hb : d52357 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11007, d52357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11007, d52357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24925 (p : Pattern) (ha : d11031 p = 1) (hb : d52387 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51923 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10686 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
    | true =>
      simp only [d10686, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10687 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10687, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10688 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10688, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11021 q = 1) (hb : d52377 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11021, d52377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11021, d52377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11030 q = 1) (hb : d52386 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11030, d52386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11030, d52386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11031 q = 1) (hb : d52387 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11031, d52387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11031, d52387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro24926 (p : Pattern) (ha : d11076 p = 1) (hb : d52398 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11032 q = 1) (hb : d52388 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11032, d52388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24925 q ha hb
    | true =>
      simp only [d11032, d52388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11033 q = 1) (hb : d52389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11033, d52389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11033, d52389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11073 q = 1) (hb : d52395 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11073, d52395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11073, d52395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11074 q = 1) (hb : d52396 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11074, d52396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11074, d52396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11075 q = 1) (hb : d52397 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11075, d52397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11075, d52397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11076 q = 1) (hb : d52398 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11076, d52398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11076, d52398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24927 (p : Pattern) (ha : d11082 p = 1) (hb : d52413 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11077 q = 1) (hb : d52408 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11077, d52408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24926 q ha hb
    | true =>
      simp only [d11077, d52408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11078 q = 1) (hb : d52409 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11078, d52409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11078, d52409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11079 q = 1) (hb : d52410 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11079, d52410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11079, d52410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11080 q = 1) (hb : d52411 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11080, d52411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11080, d52411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11081 q = 1) (hb : d52412 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11081, d52412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11081, d52412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11082 q = 1) (hb : d52413 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11082, d52413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11082, d52413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24928 (p : Pattern) (ha : d83836 p = 1) (hb : d110749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83750 q = 1) (hb : d110663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83750, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24903 q ha hb
    | true =>
      simp only [d83750, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83751 q = 1) (hb : d110664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83751, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83751, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24920 q ha hb
    | true =>
      simp only [d10870, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83833 q = 1) (hb : d110746 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83833, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83833, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83834 q = 1) (hb : d110747 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83834, d110747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83834, d110747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83835 q = 1) (hb : d110748 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83835, d110748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83835, d110748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83836 q = 1) (hb : d110749 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83836, d110749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83836, d110749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24929 (p : Pattern) (ha : d83842 p = 1) (hb : d110755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83837 q = 1) (hb : d110750 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83837, d110750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24928 q ha hb
    | true =>
      simp only [d83837, d110750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24921 q hb ha
  have h2 (q : Pattern) (ha : d83838 q = 1) (hb : d110751 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83838, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83838, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83839 q = 1) (hb : d110752 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83839, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83839, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83840 q = 1) (hb : d110753 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83840, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83840, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83841 q = 1) (hb : d110754 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83841, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83841, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83842 q = 1) (hb : d110755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83842, d110755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83842, d110755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24930 (p : Pattern) (ha : d83845 p = 1) (hb : d110758 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83750 q = 1) (hb : d110663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83750, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24903 q ha hb
    | true =>
      simp only [d83750, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83751 q = 1) (hb : d110664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83751, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83751, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24920 q ha hb
    | true =>
      simp only [d10870, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83833 q = 1) (hb : d110746 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83833, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83833, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83834 q = 1) (hb : d110747 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83834, d110747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83834, d110747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83835 q = 1) (hb : d110748 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83835, d110748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83835, d110748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83845 q = 1) (hb : d110758 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83845, d110758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83845, d110758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24931 (p : Pattern) (ha : d83851 p = 1) (hb : d110764 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83837 q = 1) (hb : d110750 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83837, d110750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24928 q ha hb
    | true =>
      simp only [d83837, d110750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24921 q hb ha
  have h2 (q : Pattern) (ha : d83838 q = 1) (hb : d110751 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83838, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83838, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83839 q = 1) (hb : d110752 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83839, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83839, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83840 q = 1) (hb : d110753 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83840, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83840, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83841 q = 1) (hb : d110754 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83841, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83841, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83846 q = 1) (hb : d110759 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83846, d110759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24930 q ha hb
    | true =>
      simp only [d83846, d110759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24922 q hb ha
  have h7 (q : Pattern) (ha : d83847 q = 1) (hb : d110760 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83847, d110760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83847, d110760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83848 q = 1) (hb : d110761 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83848, d110761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83848, d110761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d83849 q = 1) (hb : d110762 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83849, d110762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83849, d110762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83850 q = 1) (hb : d110763 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83850, d110763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83850, d110763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d83851 q = 1) (hb : d110764 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83851, d110764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83851, d110764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24932 (p : Pattern) (ha : d10902 p = 1) (hb : d52261 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10870 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24920 q ha hb
    | true =>
      simp only [d10870, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10871 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10876 q = 1) (hb : d52235 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d52235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10876, d52235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10877 q = 1) (hb : d52236 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10877, d52236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10877, d52236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10901 q = 1) (hb : d52260 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10901, d52260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10901, d52260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10902 q = 1) (hb : d52261 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10902, d52261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10902, d52261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24933 (p : Pattern) (ha : d10912 p = 1) (hb : d52271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10870 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24920 q ha hb
    | true =>
      simp only [d10870, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10871 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10876 q = 1) (hb : d52235 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d52235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10876, d52235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10910 q = 1) (hb : d52269 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10910, d52269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10910, d52269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10911 q = 1) (hb : d52270 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10911, d52270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10911, d52270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10912 q = 1) (hb : d52271 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10912, d52271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10912, d52271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24934 (p : Pattern) (ha : d83856 p = 1) (hb : d110769 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83750 q = 1) (hb : d110663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83750, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24903 q ha hb
    | true =>
      simp only [d83750, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83751 q = 1) (hb : d110664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83751, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83751, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24920 q ha hb
    | true =>
      simp only [d10870, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83833 q = 1) (hb : d110746 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83833, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83833, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83834 q = 1) (hb : d110747 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83834, d110747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83834, d110747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83855 q = 1) (hb : d110768 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83855, d110768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83855, d110768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83856 q = 1) (hb : d110769 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83856, d110769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83856, d110769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24935 (p : Pattern) (ha : d83863 p = 1) (hb : d110776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83750 q = 1) (hb : d110663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83750, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24903 q ha hb
    | true =>
      simp only [d83750, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83751 q = 1) (hb : d110664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83751, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83751, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24920 q ha hb
    | true =>
      simp only [d10870, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83833 q = 1) (hb : d110746 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83833, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83833, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83861 q = 1) (hb : d110774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83861, d110774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83861, d110774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83862 q = 1) (hb : d110775 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83862, d110775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83862, d110775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83863 q = 1) (hb : d110776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83863, d110776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83863, d110776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24936 (p : Pattern) (ha : d83868 p = 1) (hb : d110781 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52123 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10916 q = 1) (hb : d52296 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10916, d52296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77 q ha hb
    | true =>
      simp only [d10916, d52296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10917 q = 1) (hb : d52297 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10917, d52297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10917, d52297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10918 q = 1) (hb : d52298 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10918, d52298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10918, d52298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d51995 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10742 q = 1) (hb : d52124 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10742, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43 q ha hb
    | true =>
      simp only [d10742, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10743 q = 1) (hb : d52125 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10743, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10743, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10744 q = 1) (hb : d52126 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10744, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10744, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10919 q = 1) (hb : d52299 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10919, d52299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10919, d52299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83867 q = 1) (hb : d110780 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d83867, d110780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d83867, d110780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d83868 q = 1) (hb : d110781 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d83868, d110781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83868, d110781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro24937 (p : Pattern) (ha : d83874 p = 1) (hb : d110787 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83869 q = 1) (hb : d110782 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83869, d110782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24936 q ha hb
    | true =>
      simp only [d83869, d110782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83870 q = 1) (hb : d110783 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83870, d110783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83870, d110783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83750 q = 1) (hb : d110663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83750, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24903 q ha hb
    | true =>
      simp only [d83750, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83751 q = 1) (hb : d110664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83751, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83751, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83871 q = 1) (hb : d110784 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83871, d110784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83871, d110784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83872 q = 1) (hb : d110785 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83872, d110785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83872, d110785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83873 q = 1) (hb : d110786 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83873, d110786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83873, d110786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83874 q = 1) (hb : d110787 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83874, d110787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83874, d110787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24938 (p : Pattern) (ha : d83880 p = 1) (hb : d110793 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83750 q = 1) (hb : d110663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83750, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24903 q ha hb
    | true =>
      simp only [d83750, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83751 q = 1) (hb : d110664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83751, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83751, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83877 q = 1) (hb : d110790 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83877, d110790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83877, d110790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83878 q = 1) (hb : d110791 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83878, d110791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83878, d110791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83879 q = 1) (hb : d110792 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83879, d110792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83879, d110792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83880 q = 1) (hb : d110793 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83880, d110793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83880, d110793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24939 (p : Pattern) (ha : d83886 p = 1) (hb : d110799 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83857 q = 1) (hb : d110770 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83857, d110770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24934 q ha hb
    | true =>
      simp only [d83857, d110770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24932 q hb ha
  have h2 (q : Pattern) (ha : d83858 q = 1) (hb : d110771 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83858, d110771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83858, d110771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83859 q = 1) (hb : d110772 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83859, d110772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83859, d110772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83860 q = 1) (hb : d110773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83860, d110773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83860, d110773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83864 q = 1) (hb : d110777 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83864, d110777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24935 q ha hb
    | true =>
      simp only [d83864, d110777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24933 q hb ha
  have h6 (q : Pattern) (ha : d83865 q = 1) (hb : d110778 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83865, d110778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83865, d110778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83866 q = 1) (hb : d110779 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83866, d110779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83866, d110779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83875 q = 1) (hb : d110788 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83875, d110788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24937 q ha hb
    | true =>
      simp only [d83875, d110788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24928 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d83837 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d83876 q = 1) (hb : d110789 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83876, d110789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83876, d110789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d83881 q = 1) (hb : d110794 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83881, d110794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24938 q ha hb
    | true =>
      simp only [d83881, d110794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d83882 q = 1) (hb : d110795 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83882, d110795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d83882, d110795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d83883 q = 1) (hb : d110796 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83883, d110796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83883, d110796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d83884 q = 1) (hb : d110797 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83884, d110797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83884, d110797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83885 q = 1) (hb : d110798 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83885, d110798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83885, d110798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d83886 q = 1) (hb : d110799 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83886, d110799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83886, d110799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro24940 (p : Pattern) (ha : d10963 p = 1) (hb : d52317 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10870 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24920 q ha hb
    | true =>
      simp only [d10870, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10871 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10876 q = 1) (hb : d52235 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d52235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10876, d52235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10877 q = 1) (hb : d52236 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10877, d52236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10877, d52236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10901 q = 1) (hb : d52260 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10901, d52260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10901, d52260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10963 q = 1) (hb : d52317 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10963, d52317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10963, d52317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24941 (p : Pattern) (ha : d10969 p = 1) (hb : d52323 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10870 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24920 q ha hb
    | true =>
      simp only [d10870, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10871 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10876 q = 1) (hb : d52235 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d52235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10876, d52235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10910 q = 1) (hb : d52269 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10910, d52269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10910, d52269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10911 q = 1) (hb : d52270 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10911, d52270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10911, d52270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10969 q = 1) (hb : d52323 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10969, d52323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10969, d52323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24942 (p : Pattern) (ha : d83887 p = 1) (hb : d110800 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83750 q = 1) (hb : d110663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83750, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24903 q ha hb
    | true =>
      simp only [d83750, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83751 q = 1) (hb : d110664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83751, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83751, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24920 q ha hb
    | true =>
      simp only [d10870, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83833 q = 1) (hb : d110746 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83833, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83833, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83834 q = 1) (hb : d110747 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83834, d110747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83834, d110747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83855 q = 1) (hb : d110768 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83855, d110768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83855, d110768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83887 q = 1) (hb : d110800 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83887, d110800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83887, d110800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24943 (p : Pattern) (ha : d83892 p = 1) (hb : d110805 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83750 q = 1) (hb : d110663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83750, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24903 q ha hb
    | true =>
      simp only [d83750, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83751 q = 1) (hb : d110664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83751, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83751, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24920 q ha hb
    | true =>
      simp only [d10870, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83833 q = 1) (hb : d110746 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83833, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83833, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83861 q = 1) (hb : d110774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83861, d110774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83861, d110774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83862 q = 1) (hb : d110775 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83862, d110775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83862, d110775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83892 q = 1) (hb : d110805 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83892, d110805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83892, d110805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24944 (p : Pattern) (ha : d83896 p = 1) (hb : d110809 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83869 q = 1) (hb : d110782 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83869, d110782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24936 q ha hb
    | true =>
      simp only [d83869, d110782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83870 q = 1) (hb : d110783 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83870, d110783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83870, d110783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83750 q = 1) (hb : d110663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83750, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24903 q ha hb
    | true =>
      simp only [d83750, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83751 q = 1) (hb : d110664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83751, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83751, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83871 q = 1) (hb : d110784 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83871, d110784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83871, d110784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83872 q = 1) (hb : d110785 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83872, d110785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83872, d110785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83873 q = 1) (hb : d110786 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83873, d110786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83873, d110786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83896 q = 1) (hb : d110809 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83896, d110809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83896, d110809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24945 (p : Pattern) (ha : d83899 p = 1) (hb : d110812 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83750 q = 1) (hb : d110663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83750, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24903 q ha hb
    | true =>
      simp only [d83750, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83751 q = 1) (hb : d110664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83751, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83751, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83877 q = 1) (hb : d110790 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83877, d110790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83877, d110790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83878 q = 1) (hb : d110791 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83878, d110791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83878, d110791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83879 q = 1) (hb : d110792 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83879, d110792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83879, d110792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83899 q = 1) (hb : d110812 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83899, d110812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83899, d110812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24946 (p : Pattern) (ha : d83905 p = 1) (hb : d110818 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83857 q = 1) (hb : d110770 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83857, d110770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24934 q ha hb
    | true =>
      simp only [d83857, d110770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24932 q hb ha
  have h2 (q : Pattern) (ha : d83858 q = 1) (hb : d110771 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83858, d110771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83858, d110771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83859 q = 1) (hb : d110772 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83859, d110772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83859, d110772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83860 q = 1) (hb : d110773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83860, d110773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83860, d110773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83864 q = 1) (hb : d110777 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83864, d110777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24935 q ha hb
    | true =>
      simp only [d83864, d110777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24933 q hb ha
  have h6 (q : Pattern) (ha : d83865 q = 1) (hb : d110778 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83865, d110778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83865, d110778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83866 q = 1) (hb : d110779 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83866, d110779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83866, d110779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83875 q = 1) (hb : d110788 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83875, d110788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24937 q ha hb
    | true =>
      simp only [d83875, d110788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24928 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d83837 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d83876 q = 1) (hb : d110789 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83876, d110789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83876, d110789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d83881 q = 1) (hb : d110794 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83881, d110794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24938 q ha hb
    | true =>
      simp only [d83881, d110794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d83882 q = 1) (hb : d110795 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83882, d110795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d83882, d110795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d83883 q = 1) (hb : d110796 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83883, d110796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83883, d110796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d83884 q = 1) (hb : d110797 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83884, d110797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83884, d110797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83885 q = 1) (hb : d110798 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83885, d110798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83885, d110798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d83888 q = 1) (hb : d110801 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83888, d110801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24942 q ha hb
    | true =>
      simp only [d83888, d110801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24940 q hb ha
  have h17 (q : Pattern) (ha : d83889 q = 1) (hb : d110802 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83889, d110802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83889, d110802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d83890 q = 1) (hb : d110803 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83890, d110803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d83890, d110803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d83891 q = 1) (hb : d110804 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83891, d110804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83891, d110804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d83893 q = 1) (hb : d110806 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83893, d110806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24943 q ha hb
    | true =>
      simp only [d83893, d110806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24941 q hb ha
  have h21 (q : Pattern) (ha : d83894 q = 1) (hb : d110807 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83894, d110807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83894, d110807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d83895 q = 1) (hb : d110808 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83895, d110808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d83895, d110808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d83897 q = 1) (hb : d110810 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83897, d110810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24944 q ha hb
    | true =>
      simp only [d83897, d110810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24930 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d83846 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d83898 q = 1) (hb : d110811 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83898, d110811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d83898, d110811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d83900 q = 1) (hb : d110813 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83900, d110813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24945 q ha hb
    | true =>
      simp only [d83900, d110813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d83901 q = 1) (hb : d110814 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83901, d110814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d83901, d110814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d83902 q = 1) (hb : d110815 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83902, d110815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d83902, d110815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d83903 q = 1) (hb : d110816 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83903, d110816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d83903, d110816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d83904 q = 1) (hb : d110817 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83904, d110817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d83904, d110817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d83905 q = 1) (hb : d110818 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83905, d110818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d83905, d110818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro24947 (p : Pattern) (ha : d83907 p = 1) (hb : d110820 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83837 q = 1) (hb : d110750 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83837, d110750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24928 q ha hb
    | true =>
      simp only [d83837, d110750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24921 q hb ha
  have h2 (q : Pattern) (ha : d83838 q = 1) (hb : d110751 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83838, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83838, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83839 q = 1) (hb : d110752 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83839, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83839, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83840 q = 1) (hb : d110753 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83840, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83840, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83841 q = 1) (hb : d110754 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83841, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83841, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10987 q = 1) (hb : d52337 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10987, d52337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24921 q ha hb
    | true =>
      simp only [d10987, d52337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10988 q = 1) (hb : d52338 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10988, d52338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10988, d52338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10989 q = 1) (hb : d52339 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10989, d52339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10989, d52339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d10990 q = 1) (hb : d52340 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10990, d52340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10990, d52340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10991 q = 1) (hb : d52341 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10991, d52341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10991, d52341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d83907 q = 1) (hb : d110820 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83907, d110820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83907, d110820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro24948 (p : Pattern) (ha : d83914 p = 1) (hb : d110827 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83897 q = 1) (hb : d110810 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83897, d110810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24944 q ha hb
    | true =>
      simp only [d83897, d110810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24930 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83846 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83898 q = 1) (hb : d110811 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83898, d110811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83898, d110811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d83900 q = 1) (hb : d110813 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83900, d110813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24945 q ha hb
    | true =>
      simp only [d83900, d110813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83901 q = 1) (hb : d110814 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83901, d110814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83901, d110814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83902 q = 1) (hb : d110815 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83902, d110815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83902, d110815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83912 q = 1) (hb : d110825 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83912, d110825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83912, d110825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83913 q = 1) (hb : d110826 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83913, d110826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83913, d110826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83914 q = 1) (hb : d110827 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83914, d110827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83914, d110827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro24949 (p : Pattern) (ha : d83921 p = 1) (hb : d110834 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52183 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11013 q = 1) (hb : d52369 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11013, d52369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81 q ha hb
    | true =>
      simp only [d11013, d52369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11014 q = 1) (hb : d52370 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11014, d52370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11014, d52370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11015 q = 1) (hb : d52371 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11015, d52371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11015, d52371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52049 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10814 q = 1) (hb : d52184 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10814, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47 q ha hb
    | true =>
      simp only [d10814, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10815 q = 1) (hb : d52185 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10815, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10815, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10816 q = 1) (hb : d52186 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10816, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10816, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11016 q = 1) (hb : d52372 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11016, d52372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11016, d52372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83920 q = 1) (hb : d110833 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d83920, d110833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d83920, d110833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d83921 q = 1) (hb : d110834 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d83921, d110834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83921, d110834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro24950 (p : Pattern) (ha : d83927 p = 1) (hb : d110840 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83922 q = 1) (hb : d110835 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83922, d110835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24949 q ha hb
    | true =>
      simp only [d83922, d110835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83923 q = 1) (hb : d110836 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83923, d110836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83923, d110836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83803 q = 1) (hb : d110716 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83803, d110716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24914 q ha hb
    | true =>
      simp only [d83803, d110716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83804 q = 1) (hb : d110717 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83804, d110717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83804, d110717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83924 q = 1) (hb : d110837 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83924, d110837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83924, d110837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83925 q = 1) (hb : d110838 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83925, d110838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83925, d110838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83926 q = 1) (hb : d110839 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83926, d110839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83926, d110839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83927 q = 1) (hb : d110840 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83927, d110840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83927, d110840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24951 (p : Pattern) (ha : d83931 p = 1) (hb : d110844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83803 q = 1) (hb : d110716 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83803, d110716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24914 q ha hb
    | true =>
      simp only [d83803, d110716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83804 q = 1) (hb : d110717 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83804, d110717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83804, d110717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11032 q = 1) (hb : d52388 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11032, d52388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24925 q ha hb
    | true =>
      simp only [d11032, d52388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11033 q = 1) (hb : d52389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11033, d52389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11033, d52389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83928 q = 1) (hb : d110841 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83928, d110841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83928, d110841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83929 q = 1) (hb : d110842 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83929, d110842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83929, d110842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83930 q = 1) (hb : d110843 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83930, d110843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83930, d110843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83931 q = 1) (hb : d110844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83931, d110844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83931, d110844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24952 (p : Pattern) (ha : d83938 p = 1) (hb : d110850 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83803 q = 1) (hb : d110716 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83803, d110716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24914 q ha hb
    | true =>
      simp only [d83803, d110716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83804 q = 1) (hb : d110717 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83804, d110717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83804, d110717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83935 q = 1) (hb : d110847 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83935, d110847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83935, d110847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83936 q = 1) (hb : d110848 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83936, d110848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83936, d110848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83937 q = 1) (hb : d110849 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83937, d110849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83937, d110849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83938 q = 1) (hb : d110850 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83938, d110850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83938, d110850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24953 (p : Pattern) (ha : d83944 p = 1) (hb : d110856 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83932 q = 1) (hb : d110845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83932, d110845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24950 q ha hb
    | true =>
      simp only [d83932, d110845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24951 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83933 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83934 q = 1) (hb : d110846 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83934, d110846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83934, d110846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d83939 q = 1) (hb : d110851 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83939, d110851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24952 q ha hb
    | true =>
      simp only [d83939, d110851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83940 q = 1) (hb : d110852 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83940, d110852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83940, d110852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83941 q = 1) (hb : d110853 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83941, d110853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83941, d110853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83942 q = 1) (hb : d110854 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83942, d110854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83942, d110854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83943 q = 1) (hb : d110855 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83943, d110855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83943, d110855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83944 q = 1) (hb : d110856 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83944, d110856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83944, d110856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro24954 (p : Pattern) (ha : d83950 p = 1) (hb : d110862 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83843 q = 1) (hb : d110756 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83843, d110756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83843, d110756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24929 q ha hb
  have h2 (q : Pattern) (ha : d83844 q = 1) (hb : d110757 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83844, d110757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83844, d110757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d83852 q = 1) (hb : d110765 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83852, d110765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24929 q ha hb
    | true =>
      simp only [d83852, d110765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24931 q ha hb
  have h4 (q : Pattern) (ha : d83853 q = 1) (hb : d110766 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83853, d110766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83853, d110766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83854 q = 1) (hb : d110767 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83854, d110767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83854, d110767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83906 q = 1) (hb : d110819 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83906, d110819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24939 q ha hb
    | true =>
      simp only [d83906, d110819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24946 q ha hb
  have h7 (q : Pattern) (ha : d83908 q = 1) (hb : d110821 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83908, d110821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24947 q ha hb
    | true =>
      simp only [d83908, d110821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24923 q hb ha
  have h8 (q : Pattern) (ha : d83909 q = 1) (hb : d110822 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83909, d110822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83909, d110822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83910 q = 1) (hb : d110823 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83910, d110823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83910, d110823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d83911 q = 1) (hb : d110824 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83911, d110824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83911, d110824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d83915 q = 1) (hb : d110828 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83915, d110828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83915, d110828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24948 q ha hb
  have h12 (q : Pattern) (ha : d11008 q = 1) (hb : d52358 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11008, d52358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11008, d52358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24924 q ha hb
  have h13 (q : Pattern) (ha : d83916 q = 1) (hb : d110829 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83916, d110829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d83916, d110829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d83917 q = 1) (hb : d110830 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83917, d110830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d83917, d110830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d83918 q = 1) (hb : d110831 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83918, d110831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d83918, d110831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d83919 q = 1) (hb : d110832 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83919, d110832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83919, d110832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d83945 q = 1) (hb : d110857 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83945, d110857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83945, d110857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24953 q ha hb
  have h18 (q : Pattern) (ha : d11083 q = 1) (hb : d52414 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11083, d52414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11083, d52414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24927 q ha hb
  have h19 (q : Pattern) (ha : d83946 q = 1) (hb : d110858 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83946, d110858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d83946, d110858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d83947 q = 1) (hb : d110859 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83947, d110859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d83947, d110859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d83948 q = 1) (hb : d110860 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83948, d110860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d83948, d110860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d83949 q = 1) (hb : d110861 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83949, d110861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d83949, d110861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d83950 q = 1) (hb : d110862 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d83950, d110862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d83950, d110862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro24955 (p : Pattern) (ha : d83956 p = 1) (hb : d110868 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83951 q = 1) (hb : d110863 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d83951, d110863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83951, d110863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24954 q ha hb
  have h2 (q : Pattern) (ha : d83952 q = 1) (hb : d110864 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d83952, d110864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83952, d110864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83953 q = 1) (hb : d110865 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d83953, d110865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83953, d110865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d83954 q = 1) (hb : d110866 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d83954, d110866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83954, d110866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83955 q = 1) (hb : d110867 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d83955, d110867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83955, d110867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83956 q = 1) (hb : d110868 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d83956, d110868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83956, d110868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24956 (p : Pattern) (ha : d11109 p = 1) (hb : d52450 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52439 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11099 q = 1) (hb : d52440 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11099, d52440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102 q ha hb
    | true =>
      simp only [d11099, d52440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11100 q = 1) (hb : d52441 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11100, d52441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11100, d52441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11101 q = 1) (hb : d52442 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11101, d52442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11101, d52442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11103 q = 1) (hb : d52444 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11103, d52444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11103, d52444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11108 q = 1) (hb : d52449 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11108, d52449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11108, d52449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11109 q = 1) (hb : d52450 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11109, d52450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11109, d52450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro24957 (p : Pattern) (ha : d11119 p = 1) (hb : d52460 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11110 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24956 q ha hb
    | true =>
      simp only [d11110, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11111 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11116 q = 1) (hb : d52457 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d52457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11116, d52457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11117 q = 1) (hb : d52458 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11117, d52458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11117, d52458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11118 q = 1) (hb : d52459 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11118, d52459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11118, d52459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11119 q = 1) (hb : d52460 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11119, d52460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11119, d52460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24958 (p : Pattern) (ha : d11129 p = 1) (hb : d52470 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11110 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24956 q ha hb
    | true =>
      simp only [d11110, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11111 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11116 q = 1) (hb : d52457 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d52457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11116, d52457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11117 q = 1) (hb : d52458 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11117, d52458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11117, d52458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11118 q = 1) (hb : d52459 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11118, d52459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11118, d52459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11129 q = 1) (hb : d52470 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11129, d52470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11129, d52470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24959 (p : Pattern) (ha : d11249 p = 1) (hb : d52569 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11238 q = 1) (hb : d52558 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11238, d52558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24957 q ha hb
    | true =>
      simp only [d11238, d52558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11239 q = 1) (hb : d52559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11239, d52559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11239, d52559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11240 q = 1) (hb : d52560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11240, d52560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11240, d52560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11241 q = 1) (hb : d52561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11241, d52561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11241, d52561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11242 q = 1) (hb : d52562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11242, d52562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11242, d52562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11244 q = 1) (hb : d52564 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11244, d52564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24958 q ha hb
    | true =>
      simp only [d11244, d52564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11245 q = 1) (hb : d52565 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11245, d52565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11245, d52565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11246 q = 1) (hb : d52566 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11246, d52566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11246, d52566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11247 q = 1) (hb : d52567 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11247, d52567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11247, d52567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11248 q = 1) (hb : d52568 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11248, d52568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11248, d52568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11249 q = 1) (hb : d52569 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11249, d52569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11249, d52569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24960 (p : Pattern) (ha : d11258 p = 1) (hb : d52578 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11244 q = 1) (hb : d52564 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11244, d52564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24958 q ha hb
    | true =>
      simp only [d11244, d52564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11245 q = 1) (hb : d52565 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11245, d52565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11245, d52565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11246 q = 1) (hb : d52566 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11246, d52566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11246, d52566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11247 q = 1) (hb : d52567 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11247, d52567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11247, d52567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11248 q = 1) (hb : d52568 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11248, d52568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11248, d52568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11258 q = 1) (hb : d52578 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11258, d52578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11258, d52578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24961 (p : Pattern) (ha : d11289 p = 1) (hb : d52624 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52605 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11271 q = 1) (hb : d52606 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11271, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro115 q ha hb
    | true =>
      simp only [d11271, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11272 q = 1) (hb : d52607 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11272, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11272, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11273 q = 1) (hb : d52608 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11273, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11273, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11279 q = 1) (hb : d52614 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11279, d52614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11279, d52614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11288 q = 1) (hb : d52623 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11288, d52623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11288, d52623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11289 q = 1) (hb : d52624 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11289, d52624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11289, d52624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro24962 (p : Pattern) (ha : d11345 p = 1) (hb : d52635 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11290 q = 1) (hb : d52625 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11290, d52625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24961 q ha hb
    | true =>
      simp only [d11290, d52625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11291 q = 1) (hb : d52626 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11291, d52626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11291, d52626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11342 q = 1) (hb : d52632 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11342, d52632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11342, d52632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11343 q = 1) (hb : d52633 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11343, d52633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11343, d52633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11344 q = 1) (hb : d52634 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11344, d52634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11344, d52634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11345 q = 1) (hb : d52635 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11345, d52635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11345, d52635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24963 (p : Pattern) (ha : d11351 p = 1) (hb : d52650 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11346 q = 1) (hb : d52645 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11346, d52645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24962 q ha hb
    | true =>
      simp only [d11346, d52645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11347 q = 1) (hb : d52646 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11347, d52646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11347, d52646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11348 q = 1) (hb : d52647 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11348, d52647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11348, d52647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11349 q = 1) (hb : d52648 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11349, d52648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11349, d52648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11350 q = 1) (hb : d52649 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11350, d52649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11350, d52649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11351 q = 1) (hb : d52650 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11351, d52650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11351, d52650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24964 (p : Pattern) (ha : d83959 p = 1) (hb : d110871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52435 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11096 q = 1) (hb : d52436 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11096, d52436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101 q ha hb
    | true =>
      simp only [d11096, d52436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11097 q = 1) (hb : d52437 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11097, d52437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11097, d52437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11098 q = 1) (hb : d52438 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11098, d52438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11098, d52438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52439 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11099 q = 1) (hb : d52440 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11099, d52440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102 q ha hb
    | true =>
      simp only [d11099, d52440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11100 q = 1) (hb : d52441 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11100, d52441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11100, d52441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11101 q = 1) (hb : d52442 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11101, d52442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11101, d52442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11102 q = 1) (hb : d52443 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11102, d52443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11102, d52443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83958 q = 1) (hb : d110870 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d83958, d110870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d83958, d110870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d83959 q = 1) (hb : d110871 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d83959, d110871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83959, d110871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro24965 (p : Pattern) (ha : d83965 p = 1) (hb : d110877 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83960 q = 1) (hb : d110872 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83960, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24964 q ha hb
    | true =>
      simp only [d83960, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83961 q = 1) (hb : d110873 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83961, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83961, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24956 q ha hb
    | true =>
      simp only [d11110, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83962 q = 1) (hb : d110874 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83962, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83962, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83963 q = 1) (hb : d110875 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83963, d110875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83963, d110875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83964 q = 1) (hb : d110876 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83964, d110876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83964, d110876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83965 q = 1) (hb : d110877 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83965, d110877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83965, d110877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24966 (p : Pattern) (ha : d83971 p = 1) (hb : d110883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83966 q = 1) (hb : d110878 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83966, d110878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24965 q ha hb
    | true =>
      simp only [d83966, d110878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24957 q hb ha
  have h2 (q : Pattern) (ha : d83967 q = 1) (hb : d110879 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83967, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83967, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83968 q = 1) (hb : d110880 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83968, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83968, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83969 q = 1) (hb : d110881 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83969, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83969, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83970 q = 1) (hb : d110882 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83970, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83970, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83971 q = 1) (hb : d110883 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83971, d110883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83971, d110883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24967 (p : Pattern) (ha : d83974 p = 1) (hb : d110886 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83960 q = 1) (hb : d110872 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83960, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24964 q ha hb
    | true =>
      simp only [d83960, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83961 q = 1) (hb : d110873 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83961, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83961, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24956 q ha hb
    | true =>
      simp only [d11110, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83962 q = 1) (hb : d110874 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83962, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83962, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83963 q = 1) (hb : d110875 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83963, d110875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83963, d110875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83964 q = 1) (hb : d110876 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83964, d110876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83964, d110876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83974 q = 1) (hb : d110886 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83974, d110886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83974, d110886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24968 (p : Pattern) (ha : d83980 p = 1) (hb : d110892 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83966 q = 1) (hb : d110878 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83966, d110878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24965 q ha hb
    | true =>
      simp only [d83966, d110878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24957 q hb ha
  have h2 (q : Pattern) (ha : d83967 q = 1) (hb : d110879 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83967, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83967, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83968 q = 1) (hb : d110880 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83968, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83968, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83969 q = 1) (hb : d110881 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83969, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83969, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83970 q = 1) (hb : d110882 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83970, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83970, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83975 q = 1) (hb : d110887 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83975, d110887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24967 q ha hb
    | true =>
      simp only [d83975, d110887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24958 q hb ha
  have h7 (q : Pattern) (ha : d83976 q = 1) (hb : d110888 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83976, d110888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83976, d110888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83977 q = 1) (hb : d110889 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83977, d110889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83977, d110889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d83978 q = 1) (hb : d110890 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83978, d110890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83978, d110890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83979 q = 1) (hb : d110891 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83979, d110891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83979, d110891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d83980 q = 1) (hb : d110892 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83980, d110892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83980, d110892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24969 (p : Pattern) (ha : d11142 p = 1) (hb : d52483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11110 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24956 q ha hb
    | true =>
      simp only [d11110, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11111 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11116 q = 1) (hb : d52457 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d52457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11116, d52457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11117 q = 1) (hb : d52458 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11117, d52458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11117, d52458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11141 q = 1) (hb : d52482 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11141, d52482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11141, d52482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11142 q = 1) (hb : d52483 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11142, d52483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11142, d52483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24970 (p : Pattern) (ha : d11152 p = 1) (hb : d52493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11110 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24956 q ha hb
    | true =>
      simp only [d11110, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11111 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11116 q = 1) (hb : d52457 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d52457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11116, d52457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11150 q = 1) (hb : d52491 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11150, d52491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11150, d52491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11151 q = 1) (hb : d52492 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11151, d52492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11151, d52492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11152 q = 1) (hb : d52493 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11152, d52493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11152, d52493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24971 (p : Pattern) (ha : d83985 p = 1) (hb : d110897 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83960 q = 1) (hb : d110872 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83960, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24964 q ha hb
    | true =>
      simp only [d83960, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83961 q = 1) (hb : d110873 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83961, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83961, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24956 q ha hb
    | true =>
      simp only [d11110, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83962 q = 1) (hb : d110874 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83962, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83962, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83963 q = 1) (hb : d110875 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83963, d110875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83963, d110875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83984 q = 1) (hb : d110896 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83984, d110896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83984, d110896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83985 q = 1) (hb : d110897 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83985, d110897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83985, d110897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24972 (p : Pattern) (ha : d83992 p = 1) (hb : d110904 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83960 q = 1) (hb : d110872 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83960, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24964 q ha hb
    | true =>
      simp only [d83960, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83961 q = 1) (hb : d110873 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83961, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83961, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24956 q ha hb
    | true =>
      simp only [d11110, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83962 q = 1) (hb : d110874 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83962, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83962, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83990 q = 1) (hb : d110902 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83990, d110902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83990, d110902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83991 q = 1) (hb : d110903 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83991, d110903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83991, d110903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83992 q = 1) (hb : d110904 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83992, d110904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83992, d110904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24973 (p : Pattern) (ha : d83997 p = 1) (hb : d110909 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52433 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11156 q = 1) (hb : d52517 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11156, d52517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro123 q ha hb
    | true =>
      simp only [d11156, d52517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11157 q = 1) (hb : d52518 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11157, d52518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11157, d52518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11158 q = 1) (hb : d52519 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11158, d52519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11158, d52519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52435 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11096 q = 1) (hb : d52436 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11096, d52436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101 q ha hb
    | true =>
      simp only [d11096, d52436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11097 q = 1) (hb : d52437 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11097, d52437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11097, d52437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11098 q = 1) (hb : d52438 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11098, d52438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11098, d52438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11159 q = 1) (hb : d52520 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11159, d52520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11159, d52520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83996 q = 1) (hb : d110908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d83996, d110908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d83996, d110908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d83997 q = 1) (hb : d110909 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d83997, d110909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83997, d110909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro24974 (p : Pattern) (ha : d84003 p = 1) (hb : d110915 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83998 q = 1) (hb : d110910 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83998, d110910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24973 q ha hb
    | true =>
      simp only [d83998, d110910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83999 q = 1) (hb : d110911 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83999, d110911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83999, d110911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83960 q = 1) (hb : d110872 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83960, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24964 q ha hb
    | true =>
      simp only [d83960, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83961 q = 1) (hb : d110873 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83961, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83961, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84000 q = 1) (hb : d110912 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84000, d110912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84000, d110912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84001 q = 1) (hb : d110913 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84001, d110913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84001, d110913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84002 q = 1) (hb : d110914 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84002, d110914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84002, d110914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84003 q = 1) (hb : d110915 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84003, d110915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84003, d110915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24975 (p : Pattern) (ha : d84009 p = 1) (hb : d110921 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83960 q = 1) (hb : d110872 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83960, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24964 q ha hb
    | true =>
      simp only [d83960, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83961 q = 1) (hb : d110873 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83961, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83961, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84006 q = 1) (hb : d110918 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84006, d110918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84006, d110918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84007 q = 1) (hb : d110919 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84007, d110919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84007, d110919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84008 q = 1) (hb : d110920 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84008, d110920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84008, d110920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84009 q = 1) (hb : d110921 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84009, d110921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84009, d110921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24976 (p : Pattern) (ha : d84015 p = 1) (hb : d110927 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83986 q = 1) (hb : d110898 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83986, d110898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24971 q ha hb
    | true =>
      simp only [d83986, d110898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24969 q hb ha
  have h2 (q : Pattern) (ha : d83987 q = 1) (hb : d110899 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83987, d110899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83987, d110899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83988 q = 1) (hb : d110900 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83988, d110900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83988, d110900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83989 q = 1) (hb : d110901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83989, d110901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83989, d110901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83993 q = 1) (hb : d110905 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83993, d110905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24972 q ha hb
    | true =>
      simp only [d83993, d110905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24970 q hb ha
  have h6 (q : Pattern) (ha : d83994 q = 1) (hb : d110906 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83994, d110906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83994, d110906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83995 q = 1) (hb : d110907 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83995, d110907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83995, d110907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84004 q = 1) (hb : d110916 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84004, d110916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24974 q ha hb
    | true =>
      simp only [d84004, d110916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24965 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d83966 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d84005 q = 1) (hb : d110917 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84005, d110917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84005, d110917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d84010 q = 1) (hb : d110922 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84010, d110922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24975 q ha hb
    | true =>
      simp only [d84010, d110922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d84011 q = 1) (hb : d110923 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84011, d110923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84011, d110923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d84012 q = 1) (hb : d110924 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84012, d110924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84012, d110924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d84013 q = 1) (hb : d110925 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84013, d110925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84013, d110925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84014 q = 1) (hb : d110926 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84014, d110926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84014, d110926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d84015 q = 1) (hb : d110927 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84015, d110927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84015, d110927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro24977 (p : Pattern) (ha : d11214 p = 1) (hb : d52538 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11110 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24956 q ha hb
    | true =>
      simp only [d11110, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11111 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11116 q = 1) (hb : d52457 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d52457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11116, d52457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11117 q = 1) (hb : d52458 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11117, d52458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11117, d52458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11141 q = 1) (hb : d52482 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11141, d52482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11141, d52482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11214 q = 1) (hb : d52538 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11214, d52538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11214, d52538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24978 (p : Pattern) (ha : d11220 p = 1) (hb : d52544 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11110 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24956 q ha hb
    | true =>
      simp only [d11110, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11111 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11116 q = 1) (hb : d52457 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d52457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11116, d52457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11150 q = 1) (hb : d52491 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11150, d52491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11150, d52491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11151 q = 1) (hb : d52492 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11151, d52492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11151, d52492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11220 q = 1) (hb : d52544 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11220, d52544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11220, d52544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24979 (p : Pattern) (ha : d84016 p = 1) (hb : d110928 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83960 q = 1) (hb : d110872 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83960, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24964 q ha hb
    | true =>
      simp only [d83960, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83961 q = 1) (hb : d110873 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83961, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83961, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24956 q ha hb
    | true =>
      simp only [d11110, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83962 q = 1) (hb : d110874 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83962, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83962, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83963 q = 1) (hb : d110875 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83963, d110875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83963, d110875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83984 q = 1) (hb : d110896 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83984, d110896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83984, d110896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84016 q = 1) (hb : d110928 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84016, d110928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84016, d110928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24980 (p : Pattern) (ha : d84021 p = 1) (hb : d110933 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83960 q = 1) (hb : d110872 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83960, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24964 q ha hb
    | true =>
      simp only [d83960, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83961 q = 1) (hb : d110873 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83961, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83961, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24956 q ha hb
    | true =>
      simp only [d11110, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83962 q = 1) (hb : d110874 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83962, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83962, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83990 q = 1) (hb : d110902 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83990, d110902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83990, d110902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83991 q = 1) (hb : d110903 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83991, d110903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83991, d110903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84021 q = 1) (hb : d110933 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84021, d110933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84021, d110933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24981 (p : Pattern) (ha : d84025 p = 1) (hb : d110937 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83998 q = 1) (hb : d110910 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83998, d110910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24973 q ha hb
    | true =>
      simp only [d83998, d110910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83999 q = 1) (hb : d110911 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83999, d110911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83999, d110911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83960 q = 1) (hb : d110872 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83960, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24964 q ha hb
    | true =>
      simp only [d83960, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83961 q = 1) (hb : d110873 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83961, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83961, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84000 q = 1) (hb : d110912 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84000, d110912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84000, d110912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84001 q = 1) (hb : d110913 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84001, d110913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84001, d110913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84002 q = 1) (hb : d110914 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84002, d110914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84002, d110914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84025 q = 1) (hb : d110937 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84025, d110937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84025, d110937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24982 (p : Pattern) (ha : d84028 p = 1) (hb : d110940 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83960 q = 1) (hb : d110872 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83960, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24964 q ha hb
    | true =>
      simp only [d83960, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83961 q = 1) (hb : d110873 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83961, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83961, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84006 q = 1) (hb : d110918 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84006, d110918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84006, d110918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84007 q = 1) (hb : d110919 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84007, d110919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84007, d110919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84008 q = 1) (hb : d110920 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84008, d110920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84008, d110920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84028 q = 1) (hb : d110940 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84028, d110940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84028, d110940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24983 (p : Pattern) (ha : d84034 p = 1) (hb : d110946 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83986 q = 1) (hb : d110898 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83986, d110898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24971 q ha hb
    | true =>
      simp only [d83986, d110898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24969 q hb ha
  have h2 (q : Pattern) (ha : d83987 q = 1) (hb : d110899 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83987, d110899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83987, d110899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83988 q = 1) (hb : d110900 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83988, d110900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83988, d110900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83989 q = 1) (hb : d110901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83989, d110901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83989, d110901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83993 q = 1) (hb : d110905 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83993, d110905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24972 q ha hb
    | true =>
      simp only [d83993, d110905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24970 q hb ha
  have h6 (q : Pattern) (ha : d83994 q = 1) (hb : d110906 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83994, d110906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83994, d110906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83995 q = 1) (hb : d110907 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83995, d110907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83995, d110907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84004 q = 1) (hb : d110916 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84004, d110916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24974 q ha hb
    | true =>
      simp only [d84004, d110916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24965 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d83966 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d84005 q = 1) (hb : d110917 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84005, d110917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84005, d110917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d84010 q = 1) (hb : d110922 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84010, d110922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24975 q ha hb
    | true =>
      simp only [d84010, d110922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d84011 q = 1) (hb : d110923 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84011, d110923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84011, d110923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d84012 q = 1) (hb : d110924 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84012, d110924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84012, d110924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d84013 q = 1) (hb : d110925 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84013, d110925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84013, d110925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84014 q = 1) (hb : d110926 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84014, d110926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84014, d110926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d84017 q = 1) (hb : d110929 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84017, d110929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24979 q ha hb
    | true =>
      simp only [d84017, d110929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24977 q hb ha
  have h17 (q : Pattern) (ha : d84018 q = 1) (hb : d110930 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84018, d110930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84018, d110930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d84019 q = 1) (hb : d110931 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84019, d110931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84019, d110931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d84020 q = 1) (hb : d110932 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84020, d110932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84020, d110932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d84022 q = 1) (hb : d110934 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84022, d110934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24980 q ha hb
    | true =>
      simp only [d84022, d110934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24978 q hb ha
  have h21 (q : Pattern) (ha : d84023 q = 1) (hb : d110935 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84023, d110935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84023, d110935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d84024 q = 1) (hb : d110936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84024, d110936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d84024, d110936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d84026 q = 1) (hb : d110938 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84026, d110938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24981 q ha hb
    | true =>
      simp only [d84026, d110938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24967 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d83975 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d84027 q = 1) (hb : d110939 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84027, d110939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d84027, d110939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d84029 q = 1) (hb : d110941 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84029, d110941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24982 q ha hb
    | true =>
      simp only [d84029, d110941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d84030 q = 1) (hb : d110942 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84030, d110942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d84030, d110942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d84031 q = 1) (hb : d110943 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84031, d110943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d84031, d110943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d84032 q = 1) (hb : d110944 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84032, d110944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d84032, d110944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d84033 q = 1) (hb : d110945 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84033, d110945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d84033, d110945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d84034 q = 1) (hb : d110946 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84034, d110946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84034, d110946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro24984 (p : Pattern) (ha : d84036 p = 1) (hb : d110948 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83966 q = 1) (hb : d110878 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83966, d110878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24965 q ha hb
    | true =>
      simp only [d83966, d110878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24957 q hb ha
  have h2 (q : Pattern) (ha : d83967 q = 1) (hb : d110879 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83967, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83967, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83968 q = 1) (hb : d110880 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83968, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83968, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83969 q = 1) (hb : d110881 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83969, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83969, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83970 q = 1) (hb : d110882 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83970, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83970, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11238 q = 1) (hb : d52558 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11238, d52558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24957 q ha hb
    | true =>
      simp only [d11238, d52558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11239 q = 1) (hb : d52559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11239, d52559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11239, d52559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11240 q = 1) (hb : d52560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11240, d52560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11240, d52560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11241 q = 1) (hb : d52561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11241, d52561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11241, d52561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11242 q = 1) (hb : d52562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11242, d52562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11242, d52562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84036 q = 1) (hb : d110948 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84036, d110948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84036, d110948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro24985 (p : Pattern) (ha : d84043 p = 1) (hb : d110955 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84026 q = 1) (hb : d110938 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84026, d110938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24981 q ha hb
    | true =>
      simp only [d84026, d110938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24967 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83975 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84027 q = 1) (hb : d110939 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84027, d110939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84027, d110939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d84029 q = 1) (hb : d110941 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84029, d110941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24982 q ha hb
    | true =>
      simp only [d84029, d110941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84030 q = 1) (hb : d110942 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84030, d110942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84030, d110942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84031 q = 1) (hb : d110943 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84031, d110943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84031, d110943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84041 q = 1) (hb : d110953 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84041, d110953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84041, d110953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84042 q = 1) (hb : d110954 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84042, d110954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84042, d110954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84043 q = 1) (hb : d110955 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84043, d110955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84043, d110955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro24986 (p : Pattern) (ha : d84050 p = 1) (hb : d110962 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52595 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11264 q = 1) (hb : d52596 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11264, d52596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro127 q ha hb
    | true =>
      simp only [d11264, d52596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11265 q = 1) (hb : d52597 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11265, d52597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11265, d52597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11266 q = 1) (hb : d52598 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11266, d52598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11266, d52598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52600 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11267 q = 1) (hb : d52601 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11267, d52601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro128 q ha hb
    | true =>
      simp only [d11267, d52601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11268 q = 1) (hb : d52602 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11268, d52602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11268, d52602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11269 q = 1) (hb : d52603 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11269, d52603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11269, d52603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11270 q = 1) (hb : d52604 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11270, d52604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11270, d52604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84049 q = 1) (hb : d110961 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84049, d110961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d84049, d110961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d84050 q = 1) (hb : d110962 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84050, d110962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84050, d110962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro24987 (p : Pattern) (ha : d84054 p = 1) (hb : d110966 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52600 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11267 q = 1) (hb : d52601 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11267, d52601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro128 q ha hb
    | true =>
      simp only [d11267, d52601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11268 q = 1) (hb : d52602 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11268, d52602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11268, d52602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11269 q = 1) (hb : d52603 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11269, d52603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11269, d52603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52605 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11271 q = 1) (hb : d52606 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11271, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro115 q ha hb
    | true =>
      simp only [d11271, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11272 q = 1) (hb : d52607 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11272, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11272, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11273 q = 1) (hb : d52608 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11273, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11273, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11274 q = 1) (hb : d52609 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11274, d52609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11274, d52609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84053 q = 1) (hb : d110965 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84053, d110965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d84053, d110965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d84054 q = 1) (hb : d110966 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84054, d110966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84054, d110966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro24988 (p : Pattern) (ha : d84060 p = 1) (hb : d110972 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84051 q = 1) (hb : d110963 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84051, d110963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24986 q ha hb
    | true =>
      simp only [d84051, d110963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84052 q = 1) (hb : d110964 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84052, d110964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84052, d110964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84055 q = 1) (hb : d110967 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84055, d110967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24987 q ha hb
    | true =>
      simp only [d84055, d110967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84056 q = 1) (hb : d110968 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84056, d110968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84056, d110968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84057 q = 1) (hb : d110969 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84057, d110969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84057, d110969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84058 q = 1) (hb : d110970 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84058, d110970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84058, d110970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84059 q = 1) (hb : d110971 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84059, d110971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84059, d110971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84060 q = 1) (hb : d110972 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84060, d110972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84060, d110972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24989 (p : Pattern) (ha : d84064 p = 1) (hb : d110976 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84055 q = 1) (hb : d110967 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84055, d110967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24987 q ha hb
    | true =>
      simp only [d84055, d110967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84056 q = 1) (hb : d110968 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84056, d110968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84056, d110968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11290 q = 1) (hb : d52625 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11290, d52625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24961 q ha hb
    | true =>
      simp only [d11290, d52625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11291 q = 1) (hb : d52626 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11291, d52626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11291, d52626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84061 q = 1) (hb : d110973 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84061, d110973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84061, d110973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84062 q = 1) (hb : d110974 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84062, d110974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84062, d110974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84063 q = 1) (hb : d110975 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84063, d110975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84063, d110975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84064 q = 1) (hb : d110976 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84064, d110976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84064, d110976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24990 (p : Pattern) (ha : d84071 p = 1) (hb : d110982 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84055 q = 1) (hb : d110967 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84055, d110967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24987 q ha hb
    | true =>
      simp only [d84055, d110967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84056 q = 1) (hb : d110968 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84056, d110968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84056, d110968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84068 q = 1) (hb : d110979 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84068, d110979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84068, d110979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84069 q = 1) (hb : d110980 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84069, d110980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84069, d110980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84070 q = 1) (hb : d110981 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84070, d110981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84070, d110981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84071 q = 1) (hb : d110982 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84071, d110982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84071, d110982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24991 (p : Pattern) (ha : d84077 p = 1) (hb : d110988 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84065 q = 1) (hb : d110977 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84065, d110977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24988 q ha hb
    | true =>
      simp only [d84065, d110977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24989 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84066 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84067 q = 1) (hb : d110978 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84067, d110978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84067, d110978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d84072 q = 1) (hb : d110983 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84072, d110983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24990 q ha hb
    | true =>
      simp only [d84072, d110983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84073 q = 1) (hb : d110984 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84073, d110984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84073, d110984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84074 q = 1) (hb : d110985 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84074, d110985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84074, d110985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84075 q = 1) (hb : d110986 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84075, d110986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84075, d110986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84076 q = 1) (hb : d110987 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84076, d110987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84076, d110987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84077 q = 1) (hb : d110988 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84077, d110988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84077, d110988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro24992 (p : Pattern) (ha : d84083 p = 1) (hb : d110994 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83972 q = 1) (hb : d110884 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83972, d110884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83972, d110884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24966 q ha hb
  have h2 (q : Pattern) (ha : d83973 q = 1) (hb : d110885 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83973, d110885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83973, d110885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d83981 q = 1) (hb : d110893 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83981, d110893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24966 q ha hb
    | true =>
      simp only [d83981, d110893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24968 q ha hb
  have h4 (q : Pattern) (ha : d83982 q = 1) (hb : d110894 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83982, d110894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83982, d110894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83983 q = 1) (hb : d110895 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83983, d110895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83983, d110895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84035 q = 1) (hb : d110947 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84035, d110947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24976 q ha hb
    | true =>
      simp only [d84035, d110947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24983 q ha hb
  have h7 (q : Pattern) (ha : d84037 q = 1) (hb : d110949 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84037, d110949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24984 q ha hb
    | true =>
      simp only [d84037, d110949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24959 q hb ha
  have h8 (q : Pattern) (ha : d84038 q = 1) (hb : d110950 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84038, d110950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84038, d110950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84039 q = 1) (hb : d110951 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84039, d110951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84039, d110951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d84040 q = 1) (hb : d110952 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84040, d110952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84040, d110952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84044 q = 1) (hb : d110956 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84044, d110956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84044, d110956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24985 q ha hb
  have h12 (q : Pattern) (ha : d11259 q = 1) (hb : d52579 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11259, d52579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11259, d52579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24960 q ha hb
  have h13 (q : Pattern) (ha : d84045 q = 1) (hb : d110957 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84045, d110957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84045, d110957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d84046 q = 1) (hb : d110958 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84046, d110958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84046, d110958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d84047 q = 1) (hb : d110959 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84047, d110959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d84047, d110959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d84048 q = 1) (hb : d110960 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84048, d110960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84048, d110960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d84078 q = 1) (hb : d110989 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84078, d110989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84078, d110989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24991 q ha hb
  have h18 (q : Pattern) (ha : d11352 q = 1) (hb : d52651 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11352, d52651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11352, d52651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24963 q ha hb
  have h19 (q : Pattern) (ha : d84079 q = 1) (hb : d110990 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84079, d110990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84079, d110990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d84080 q = 1) (hb : d110991 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84080, d110991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d84080, d110991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d84081 q = 1) (hb : d110992 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84081, d110992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d84081, d110992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d84082 q = 1) (hb : d110993 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84082, d110993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d84082, d110993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d84083 q = 1) (hb : d110994 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d84083, d110994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d84083, d110994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro24993 (p : Pattern) (ha : d84089 p = 1) (hb : d111000 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84084 q = 1) (hb : d110995 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d84084, d110995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84084, d110995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24992 q ha hb
  have h2 (q : Pattern) (ha : d84085 q = 1) (hb : d110996 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d84085, d110996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84085, d110996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84086 q = 1) (hb : d110997 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d84086, d110997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84086, d110997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84087 q = 1) (hb : d110998 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d84087, d110998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84087, d110998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84088 q = 1) (hb : d110999 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d84088, d110999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84088, d110999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84089 q = 1) (hb : d111000 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d84089, d111000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84089, d111000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24994 (p : Pattern) (ha : d11379 p = 1) (hb : d52733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52722 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11369 q = 1) (hb : d52723 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11369, d52723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro153 q ha hb
    | true =>
      simp only [d11369, d52723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11370 q = 1) (hb : d52724 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11370, d52724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11370, d52724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11371 q = 1) (hb : d52725 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11371, d52725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11371, d52725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11373 q = 1) (hb : d52727 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11373, d52727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11373, d52727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11378 q = 1) (hb : d52732 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11378, d52732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11378, d52732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11379 q = 1) (hb : d52733 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11379, d52733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11379, d52733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro24995 (p : Pattern) (ha : d11389 p = 1) (hb : d52743 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11380 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24994 q ha hb
    | true =>
      simp only [d11380, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11381 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11386 q = 1) (hb : d52740 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11386, d52740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11386, d52740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11387 q = 1) (hb : d52741 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11387, d52741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11387, d52741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11388 q = 1) (hb : d52742 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11388, d52742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11388, d52742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11389 q = 1) (hb : d52743 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11389, d52743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11389, d52743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24996 (p : Pattern) (ha : d11399 p = 1) (hb : d52753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11380 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24994 q ha hb
    | true =>
      simp only [d11380, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11381 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11386 q = 1) (hb : d52740 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11386, d52740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11386, d52740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11387 q = 1) (hb : d52741 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11387, d52741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11387, d52741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11388 q = 1) (hb : d52742 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11388, d52742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11388, d52742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11399 q = 1) (hb : d52753 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11399, d52753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11399, d52753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24997 (p : Pattern) (ha : d11519 p = 1) (hb : d52849 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11508 q = 1) (hb : d52838 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11508, d52838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24995 q ha hb
    | true =>
      simp only [d11508, d52838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11509 q = 1) (hb : d52839 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11509, d52839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11509, d52839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11510 q = 1) (hb : d52840 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11510, d52840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11510, d52840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11511 q = 1) (hb : d52841 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11511, d52841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11511, d52841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11512 q = 1) (hb : d52842 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11512, d52842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11512, d52842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11514 q = 1) (hb : d52844 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11514, d52844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24996 q ha hb
    | true =>
      simp only [d11514, d52844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11515 q = 1) (hb : d52845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11515, d52845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11515, d52845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11516 q = 1) (hb : d52846 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11516, d52846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11516, d52846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11517 q = 1) (hb : d52847 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11517, d52847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11517, d52847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11518 q = 1) (hb : d52848 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11518, d52848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11518, d52848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11519 q = 1) (hb : d52849 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11519, d52849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11519, d52849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24998 (p : Pattern) (ha : d11528 p = 1) (hb : d52858 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11514 q = 1) (hb : d52844 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11514, d52844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24996 q ha hb
    | true =>
      simp only [d11514, d52844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11515 q = 1) (hb : d52845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11515, d52845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11515, d52845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11516 q = 1) (hb : d52846 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11516, d52846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11516, d52846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11517 q = 1) (hb : d52847 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11517, d52847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11517, d52847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11518 q = 1) (hb : d52848 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11518, d52848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11518, d52848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11528 q = 1) (hb : d52858 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11528, d52858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11528, d52858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24999 (p : Pattern) (ha : d11559 p = 1) (hb : d52918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52899 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11541 q = 1) (hb : d52900 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11541, d52900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro167 q ha hb
    | true =>
      simp only [d11541, d52900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11542 q = 1) (hb : d52901 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11542, d52901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11542, d52901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11543 q = 1) (hb : d52902 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11543, d52902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11543, d52902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11549 q = 1) (hb : d52908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11549, d52908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11549, d52908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11558 q = 1) (hb : d52917 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11558, d52917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11558, d52917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11559 q = 1) (hb : d52918 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11559, d52918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11559, d52918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
end NetHack.Soko22Hazard87
